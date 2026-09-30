//! `clif-native --diff`: differential testing of a prebuilt object (the Lean backend's)
//! against Cranelift's own aarch64 code for the same CLIF file, over generated inputs.
//!
//! usage: clif-native --diff <file.clif> --lean-obj <obj> --lean-table <json>
//!            [--link <obj>]... [--alias SYM=TARGET]... [--vectors N] [--min-vectors N]
//!            [--max-vectors N] [--seed S] [--call-timeout-ms MS] [--jobs J] [--keep DIR]
//!            [--only SYMBOL]... [--lean-only SYMBOL]...
//!
//! Every function of the file is called with generated inputs in two executables that differ
//! only in the object holding the file's functions: engine `lean` (`--lean-obj`) and engine
//! `cranelift` (every function compiled here, as plain `clif-native` does). Both link the
//! same freestanding harness (`diffharness.c`), the same Cranelift-compiled trampolines, the
//! file's `; data:` objects (at fixed addresses), the `--link` runtime objects and generated
//! stubs for the remaining undefined symbols:
//!   * `--alias SYM=TARGET` and the Rust allocator entry points (`__rust_alloc`, ...,
//!     mangled or not) jump to TARGET / the harness's bump allocator;
//!   * a symbol the file only uses as data (`symbol_value`, `; data:` items) is an absolute
//!     address in an unmapped page (dead references whose object cg_clif dropped);
//!   * any other function is a stub that traps (`udf`): the outcome `extern <symbol>` (the
//!     `core` panic entry points never return, so this is exact for them).
//! Pointer parameters are inferred from the CLIF (a parameter that flows, through
//! `iadd`/`isub`/`select`/block arguments/stack slots/calls, into a load or store address or
//! a `mem*` pointer argument).
//!
//! Each (function, vector) runs under two stack configurations per engine. Outcomes:
//! `agree` (the four runs agree), `disagree` (both engines are deterministic but differ), or
//! skipped: `timeout`, `stack overflow`, `nondeterministic` (one engine's two configurations
//! differ: the result depends on uninitialised stack/heap bytes or on stack addresses, which
//! CLIF leaves unspecified), `crash` (the harness process died). A function with fewer than
//! `--min-vectors` compared vectors gets more vectors, up to `--max-vectors`.
//!
//! Output: one JSON record per function and a final `{"summary": ...}` record on stdout;
//! exit status 0 iff there is no disagreement.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::Read;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context as _, Result, anyhow, bail};
use clif2obj::{ObjectCompiler, Options};
use cranelift_codegen::ir::{
    ArgumentPurpose, Block, ExternalName, Function, InstructionData, Opcode, Type, Value, instructions::CallInfo,
};
use object::{Object, ObjectSymbol};
use parking_lot::Mutex;
use serde_json::{Value as Json, json};

use super::{SLOT, TRIPLE, Tools, c_string, data_asm, panic_message, read_table, run_tool, signal_name, trampoline};

const DIFF_HARNESS_C: &str = include_str!("diffharness.c");
/// Fixed addresses of the `; data:` objects (identical in both executables).
const RO_ADDR: u64 = 0x2000_0000;
const RW_ADDR: u64 = 0x2800_0000;
/// The per-function thunks (diffharness.c `clifdiff_thunks`).
const THUNK_ADDR: u64 = 0x2c00_0000;
/// The thunks' target table.
const FNPTR_ADDR: u64 = 0x2e00_0000;
/// The stubs of undefined functions.
const STUB_ADDR: u64 = 0x2d00_0000;
/// Unmapped page range for dead data-symbol references.
const DEAD_DATA_ADDR: u64 = 0x3000_0000;
/// Harness regions (diffharness.c).
const STACK_BASE: u64 = 0x7_d000_0000;
const STACK_SIZE: u64 = 32 << 20;

const USAGE: &str = "usage: clif-native --diff <file.clif> --lean-obj <obj> --lean-table <json> [--link <obj>]... \
     [--alias SYM=TARGET]... [--vectors N] [--min-vectors N] [--max-vectors N] [--seed S] [--call-timeout-ms MS] \
     [--jobs J] [--keep DIR] [--only SYMBOL]... [--lean-only SYMBOL]...";

/// Rust allocator entry points, by the suffix of their (possibly mangled) symbol.
const ALLOCATOR: &[(&str, &str)] = &[
    ("__rust_alloc", "clifdiff_rust_alloc"),
    ("__rust_alloc_zeroed", "clifdiff_rust_alloc_zeroed"),
    ("__rust_dealloc", "clifdiff_rust_dealloc"),
    ("__rust_realloc", "clifdiff_rust_realloc"),
    ("__rust_no_alloc_shim_is_unstable_v2", "clifdiff_rust_noop"),
];

struct DiffConfig {
    file: String,
    lean_obj: PathBuf,
    lean_table: PathBuf,
    links: Vec<PathBuf>,
    aliases: HashMap<String, String>,
    vectors: u32,
    min_vectors: u32,
    max_vectors: u32,
    seed: u64,
    call_timeout_us: u64,
    jobs: usize,
    keep: Option<PathBuf>,
    only: Vec<String>,
    /// `--lean-only`: the lean engine takes only these functions from the Lean object (the
    /// rest from Cranelift), to bisect a disagreement down to the function whose Lean code
    /// causes it.
    lean_only: Vec<String>,
    tools: Tools,
}

fn parse_diff_args(args: &[String]) -> Result<DiffConfig> {
    let mut it = args.iter();
    let mut file = None;
    let (mut lean_obj, mut lean_table) = (None, None);
    let mut cfg = DiffConfig {
        file: String::new(),
        lean_obj: PathBuf::new(),
        lean_table: PathBuf::new(),
        links: Vec::new(),
        aliases: HashMap::new(),
        vectors: 64,
        min_vectors: 50,
        max_vectors: 512,
        seed: 0x5eed,
        call_timeout_us: 500_000,
        jobs: 2,
        keep: None,
        only: Vec::new(),
        lean_only: Vec::new(),
        tools: Tools::from_env(),
    };
    while let Some(a) = it.next() {
        let mut value = || it.next().cloned().ok_or_else(|| anyhow!("{a} needs a value\n{USAGE}"));
        match a.as_str() {
            "--lean-obj" => lean_obj = Some(PathBuf::from(value()?)),
            "--lean-table" => lean_table = Some(PathBuf::from(value()?)),
            "--link" => cfg.links.push(PathBuf::from(value()?)),
            "--alias" => {
                let v = value()?;
                let (s, t) = v.split_once('=').ok_or_else(|| anyhow!("--alias SYM=TARGET, got {v}"))?;
                cfg.aliases.insert(s.to_string(), t.to_string());
            }
            "--vectors" => cfg.vectors = value()?.parse().context("--vectors")?,
            "--min-vectors" => cfg.min_vectors = value()?.parse().context("--min-vectors")?,
            "--max-vectors" => cfg.max_vectors = value()?.parse().context("--max-vectors")?,
            "--seed" => cfg.seed = value()?.parse().context("--seed")?,
            "--call-timeout-ms" => cfg.call_timeout_us = value()?.parse::<u64>().context("--call-timeout-ms")? * 1000,
            "--jobs" => cfg.jobs = value()?.parse::<usize>().context("--jobs")?.max(1),
            "--keep" => cfg.keep = Some(PathBuf::from(value()?)),
            "--only" => cfg.only.push(value()?),
            "--lean-only" => cfg.lean_only.push(value()?),
            s if s.starts_with("--") => bail!("unknown option {s}\n{USAGE}"),
            _ if file.is_none() => file = Some(a.clone()),
            _ => bail!("{USAGE}"),
        }
    }
    cfg.file = file.ok_or_else(|| anyhow!("{USAGE}"))?;
    cfg.lean_obj = lean_obj.ok_or_else(|| anyhow!("--lean-obj is required\n{USAGE}"))?;
    cfg.lean_table = lean_table.ok_or_else(|| anyhow!("--lean-table is required\n{USAGE}"))?;
    cfg.max_vectors = cfg.max_vectors.max(cfg.vectors);
    Ok(cfg)
}

/// Parameter kinds of the harness (`pdesc`): 0 integer, 1 pointer, 2 `sret` pointer, 3 code
/// pointer (called with `call_indirect`), 4 pointer to a table of code pointers (a vtable).
/// Returns, per function and parameter, the kind and (kind 3) the signature it is called with.
fn param_kinds(funcs: &[&Function], index: &HashMap<String, usize>) -> Vec<Vec<(u8, Option<String>)>> {
    let resolve = |f: &Function, v: Value| f.dfg.resolve_aliases(v);
    // Per function: flow edges (from, to) and address sinks; calls: (arg, callee, param).
    struct Flow {
        edges: Vec<(Value, Value)>,
        sinks: Vec<Value>,
        /// `call_indirect` callees
        code: Vec<Value>,
        /// their signatures (as text)
        code_sigs: HashMap<Value, String>,
        /// loads: (address, result)
        loads: Vec<(Value, Value)>,
        calls: Vec<(Value, usize, usize)>,
    }
    let mut flows = Vec::new();
    for f in funcs {
        let mut fl = Flow { edges: Vec::new(), sinks: Vec::new(), code: Vec::new(), code_sigs: HashMap::new(), loads: Vec::new(), calls: Vec::new() };
        let dfg = &f.dfg;
        // stack_addr results, by value: (slot, offset)
        let mut slot_addr: HashMap<Value, (u32, i64)> = HashMap::new();
        let mut slot_stores: HashMap<(u32, i64), Vec<Value>> = HashMap::new();
        let mut slot_loads: HashMap<(u32, i64), Vec<Value>> = HashMap::new();
        for block in f.layout.blocks() {
            for inst in f.layout.block_insts(block) {
                let data = &dfg.insts[inst];
                let results: Vec<Value> = dfg.inst_results(inst).to_vec();
                let args: Vec<Value> = dfg.inst_args(inst).iter().map(|&v| resolve(f, v)).collect();
                match *data {
                    InstructionData::StackAddr { stack_slot, offset, .. } => {
                        slot_addr.insert(results[0], (stack_slot.as_u32(), i64::from(offset)));
                    }
                    InstructionData::Load { offset, .. } => {
                        fl.sinks.push(args[0]);
                        fl.loads.push((args[0], results[0]));
                        if let Some(&(s, o)) = slot_addr.get(&args[0]) {
                            slot_loads.entry((s, o + i64::from(offset))).or_default().extend(&results);
                        }
                    }
                    InstructionData::LoadNoOffset { .. } => fl.sinks.push(args[0]),
                    InstructionData::Store { offset, .. } => {
                        fl.sinks.push(args[1]);
                        if let Some(&(s, o)) = slot_addr.get(&args[1]) {
                            slot_stores.entry((s, o + i64::from(offset))).or_default().push(args[0]);
                        }
                    }
                    InstructionData::StoreNoOffset { .. } => fl.sinks.push(args[1]),
                    InstructionData::AtomicRmw { .. } | InstructionData::AtomicCas { .. } => fl.sinks.push(args[0]),
                    InstructionData::Binary { opcode: Opcode::Iadd, .. } => {
                        fl.edges.push((args[0], results[0]));
                        fl.edges.push((args[1], results[0]));
                    }
                    InstructionData::Binary { opcode: Opcode::Isub, .. } => fl.edges.push((args[0], results[0])),
                    InstructionData::Ternary { opcode: Opcode::Select, .. } => {
                        fl.edges.push((args[1], results[0]));
                        fl.edges.push((args[2], results[0]));
                    }
                    InstructionData::Unary { opcode: Opcode::Bitcast, .. } => fl.edges.push((args[0], results[0])),
                    _ => {}
                }
                if let InstructionData::CallIndirect { sig_ref, .. } = data {
                    fl.code.push(args[0]);
                    fl.code_sigs.insert(args[0], dfg.signatures[*sig_ref].to_string());
                    // the first argument of an indirect call is usually `self` of a dyn method
                    if args.len() > 1 && dfg.value_type(args[1]).bits() == 64 {
                        fl.sinks.push(args[1]);
                    }
                }
                if let CallInfo::Direct(fref, cargs) = data.analyze_call(&dfg.value_lists, &dfg.exception_tables) {
                    let name = match &dfg.ext_funcs[fref].name {
                        ExternalName::TestCase(t) => t.to_string().trim_start_matches('%').to_string(),
                        _ => String::new(),
                    };
                    let cargs: Vec<Value> = cargs.iter().map(|&v| resolve(f, v)).collect();
                    let ptr_args: &[usize] = match name.as_str() {
                        "memcpy" | "memmove" | "memcmp" | "bcmp" => &[0, 1],
                        "memset" => &[0],
                        _ => &[],
                    };
                    for &j in ptr_args {
                        if let Some(&a) = cargs.get(j) {
                            fl.sinks.push(a);
                        }
                    }
                    if let Some(&g) = index.get(&name) {
                        for (j, &a) in cargs.iter().enumerate() {
                            fl.calls.push((a, g, j));
                        }
                    }
                }
                for dest in data.branch_destination(&dfg.jump_tables, &dfg.exception_tables) {
                    let target: Block = dest.block(&dfg.value_lists);
                    let params = dfg.block_params(target);
                    for (k, a) in dest.args(&dfg.value_lists).enumerate() {
                        if let (Some(v), Some(&p)) = (a.as_value(), params.get(k)) {
                            fl.edges.push((resolve(f, v), p));
                        }
                    }
                }
            }
        }
        for (key, stored) in &slot_stores {
            for &l in slot_loads.get(key).map(Vec::as_slice).unwrap_or(&[]) {
                for &s in stored {
                    fl.edges.push((s, l));
                }
            }
        }
        flows.push(fl);
    }
    // Three backward properties: used as an address (`ptr`), called (`code`), and the address
    // of a loaded callee (`table`: a vtable / function-pointer table).
    let seed = |f: &dyn Fn(&Flow) -> Vec<Value>| -> Vec<HashSet<Value>> { flows.iter().map(|fl| f(fl).into_iter().collect()).collect() };
    let mut sets: [Vec<HashSet<Value>>; 3] = [seed(&|fl| fl.sinks.clone()), seed(&|fl| fl.code.clone()), seed(&|_| Vec::new())];
    let entry_params = |g: usize| -> Vec<Value> {
        let f = funcs[g];
        f.layout.entry_block().map(|b| f.dfg.block_params(b).to_vec()).unwrap_or_default()
    };
    let params: Vec<Vec<Value>> = (0..funcs.len()).map(entry_params).collect();
    loop {
        let mut changed = false;
        for i in 0..funcs.len() {
            for &(addr, result) in &flows[i].loads {
                if sets[1][i].contains(&result) && sets[2][i].insert(addr) {
                    changed = true;
                }
            }
            for set in sets.iter_mut() {
                for &(from, to) in &flows[i].edges {
                    if set[i].contains(&to) && set[i].insert(from) {
                        changed = true;
                    }
                }
                for &(a, g, j) in &flows[i].calls {
                    let callee = params[g].get(j).is_some_and(|p| set[g].contains(p));
                    if callee && set[i].insert(a) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    let [ptr, code, table] = sets;
    // The signature a code-pointer parameter is called with: forward along the flow edges and
    // calls to the first `call_indirect` it reaches.
    let called_sig = |i: usize, v: Value| -> Option<String> {
        let mut seen: HashSet<(usize, Value)> = HashSet::new();
        let mut todo = vec![(i, v)];
        while let Some((g, x)) = todo.pop() {
            if !seen.insert((g, x)) {
                continue;
            }
            if let Some(sg) = flows[g].code_sigs.get(&x) {
                return Some(sg.clone());
            }
            todo.extend(flows[g].edges.iter().filter(|e| e.0 == x).map(|e| (g, e.1)));
            for &(a, h, j) in &flows[g].calls {
                if a == x {
                    if let Some(&p) = params[h].get(j) {
                        todo.push((h, p));
                    }
                }
            }
        }
        None
    };
    funcs
        .iter()
        .enumerate()
        .map(|(i, f)| {
            f.signature
                .params
                .iter()
                .enumerate()
                .map(|(j, p)| {
                    let has = |set: &Vec<HashSet<Value>>| params[i].get(j).is_some_and(|v| set[i].contains(v));
                    if p.purpose == ArgumentPurpose::StructReturn {
                        (2, None)
                    } else if p.value_type.bits() != 64 {
                        (0, None)
                    } else if has(&code) {
                        (3, called_sig(i, params[i][j]))
                    } else if has(&table) {
                        (4, None)
                    } else if has(&ptr) {
                        (1, None)
                    } else {
                        (0, None)
                    }
                })
                .collect()
        })
        .collect()
}

/// Defined and undefined global symbols of an ELF object (or of every member of an archive).
fn object_symbols(path: &Path) -> Result<(HashSet<String>, HashSet<String>)> {
    let bytes = std::fs::read(path).with_context(|| format!("reading {}", path.display()))?;
    let mut defined = HashSet::new();
    let mut undefined = HashSet::new();
    let mut scan = |data: &[u8]| -> Result<()> {
        let file = object::File::parse(data).with_context(|| format!("parsing {}", path.display()))?;
        for s in file.symbols() {
            let Ok(name) = s.name() else { continue };
            if name.is_empty() {
                continue;
            }
            if s.is_undefined() {
                // weak references (e.g. the harness's `__start_clifd_rw`) may stay undefined
                if !s.is_weak() {
                    undefined.insert(name.to_string());
                }
            } else if s.is_global() {
                defined.insert(name.to_string());
            }
        }
        Ok(())
    };
    if bytes.starts_with(b"!<arch>\n") {
        let ar = object::read::archive::ArchiveFile::parse(&*bytes)?;
        for m in ar.members() {
            let m = m?;
            scan(m.data(&*bytes)?)?;
        }
    } else {
        scan(&bytes)?;
    }
    Ok((defined, undefined))
}

/// A linked executable: path and its symbols sorted by address (address, size, name).
struct Exe {
    path: PathBuf,
    syms: Vec<(u64, u64, String)>,
    /// Trap sites of the file's functions: name -> offset -> trap code.
    traps: HashMap<String, HashMap<u32, String>>,
    /// The trapping stubs of undefined functions.
    stubs: HashSet<String>,
}

impl Exe {
    fn load(path: PathBuf, traps: HashMap<String, HashMap<u32, String>>, stubs: HashSet<String>) -> Result<Exe> {
        let bytes = std::fs::read(&path)?;
        let file = object::File::parse(&*bytes)?;
        let mut syms: Vec<(u64, u64, String)> = file
            .symbols()
            .filter(|s| s.is_definition() && !s.name().unwrap_or("").is_empty())
            .filter(|s| s.kind() == object::SymbolKind::Text || s.kind() == object::SymbolKind::Unknown)
            .map(|s| (s.address(), s.size(), s.name().unwrap_or("").to_string()))
            .collect();
        syms.sort();
        Ok(Exe { path, syms, traps, stubs })
    }

    /// The symbol containing `pc`: name and offset.
    fn symbolize(&self, pc: u64) -> Option<(&str, u64)> {
        let i = self.syms.partition_point(|s| s.0 <= pc);
        let (addr, size, name) = self.syms.get(i.checked_sub(1)?)?;
        let off = pc - addr;
        (off < (*size).max(8)).then_some((name.as_str(), off))
    }
}

/// One run's outcome.
#[derive(Clone, Debug)]
enum Outcome {
    /// kind 0 (returned) or 1 (signal)
    Ran(Run),
    Timeout,
    Overflow,
    Crash(String),
}

#[derive(Clone, Debug)]
struct Run {
    /// `returned`, `trap <code>`, `extern <symbol>`, `SIGSEGV in <symbol>`, ...
    class: String,
    fault: Option<String>,
    results: Vec<u8>,
    heap: u64,
    /// observable memory words: address -> (initial, final)
    mem: BTreeMap<u64, (u64, u64)>,
    truncated: bool,
    hash: u64,
}

impl Run {
    /// Everything but the bit patterns of results and memory.
    fn shape(&self) -> (&str, &Option<String>, u64, bool, usize) {
        (&self.class, &self.fault, self.heap, self.truncated, self.results.len())
    }
    fn word(&self, addr: u64, init: u64) -> u64 {
        self.mem.get(&addr).map_or(init, |e| e.1)
    }
}

impl Outcome {
    fn json(&self) -> Json {
        match self {
            Outcome::Ran(r) => json!({
                "class": r.class, "fault": r.fault, "results": hex(&r.results), "heap_used": r.heap,
                "memory_words_written": r.mem.len(), "memory_hash": format!("{:016x}", r.hash),
            }),
            Outcome::Timeout => json!("timeout"),
            Outcome::Overflow => json!("stack overflow"),
            Outcome::Crash(s) => json!({"crash": s}),
        }
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

struct FnInfo {
    name: String,
    /// result byte ranges within the 32-byte result area
    ret_bytes: Vec<(usize, usize)>,
}

/// Header bytes of a harness record (diffharness.c `struct rec`); 24 bytes per memory entry.
const HEADER: usize = 72;

/// Parses one record at the start of `rec`: key, outcome and record length (`None` if the
/// record is incomplete).
fn parse_record(exe: &Exe, info: &[FnInfo], rec: &[u8]) -> Option<((u32, u32, u32), Outcome, usize)> {
    if rec.len() < HEADER {
        return None;
    }
    let u32_at = |at: usize| u32::from_le_bytes(rec[at..at + 4].try_into().unwrap());
    let u64_at = |at: usize| u64::from_le_bytes(rec[at..at + 8].try_into().unwrap());
    let (f, v, c, kind) = (u32_at(0), u32_at(4), u32_at(8), u32_at(12));
    let (heap, nmem, truncated, hash) = (u64_at(48), u32_at(56) as usize, u32_at(60) != 0, u64_at(64));
    let len = HEADER + 24 * nmem;
    if rec.len() < len {
        return None;
    }
    let mem = (0..nmem)
        .map(|k| {
            let at = HEADER + 24 * k;
            (u64_at(at), (u64_at(at + 8), u64_at(at + 16)))
        })
        .collect();
    let x = &rec[16..48];
    let run = |class: String, fault: Option<String>, results: Vec<u8>| {
        Outcome::Ran(Run { class, fault, results, heap, mem, truncated, hash })
    };
    let out = match kind {
        0 => {
            let mut results = Vec::new();
            if let Some(fi) = info.get(f as usize) {
                for &(a, b) in &fi.ret_bytes {
                    results.extend_from_slice(&x[a..b]);
                }
            }
            run("returned".into(), None, results)
        }
        1 => {
            let (signo, pc, addr) = (u64_at(16), u64_at(24), u64_at(32));
            let sig = signal_name(signo as u32);
            let class = match exe.symbolize(pc) {
                Some((name, off)) => match exe.traps.get(name) {
                    Some(t) => match u32::try_from(off).ok().and_then(|o| t.get(&o)) {
                        Some(code) => format!("trap {code}"),
                        None => format!("{sig} in %{name}"),
                    },
                    None if exe.stubs.contains(name) => format!("extern {name}"),
                    None => format!("{sig} in {name}"),
                },
                None => format!("{sig} at pc {pc:#x}"),
            };
            let fault = matches!(signo, 7 | 11).then(|| {
                if (STACK_BASE..STACK_BASE + STACK_SIZE).contains(&addr) {
                    "stack".to_string()
                } else {
                    match exe.symbolize(addr) {
                        Some((name, off)) if addr == pc => format!("pc {name}+{off:#x}"),
                        _ => format!("{addr:#x}"),
                    }
                }
            });
            run(class, fault, Vec::new())
        }
        2 => Outcome::Timeout,
        3 => Outcome::Overflow,
        k => Outcome::Crash(format!("bad record kind {k}")),
    };
    Some(((f, v, c), out, len))
}

/// The verdict for one vector from its four runs (engine A = lean, B = cranelift; configs 0/1).
enum Verdict {
    /// `masked`: some bits were not compared (they depend on uninitialised bytes).
    Agree { class: String, masked: bool },
    Disagree(Json),
    Skip(&'static str),
}

fn compare(a0: &Outcome, a1: &Outcome, b0: &Outcome, b1: &Outcome) -> Verdict {
    let all = [a0, a1, b0, b1];
    if all.iter().any(|o| matches!(o, Outcome::Crash(_))) {
        return Verdict::Skip("crash");
    }
    if all.iter().any(|o| matches!(o, Outcome::Timeout)) {
        return Verdict::Skip("timeout");
    }
    if all.iter().any(|o| matches!(o, Outcome::Overflow)) {
        return Verdict::Skip("stack overflow");
    }
    let (Outcome::Ran(ra0), Outcome::Ran(ra1), Outcome::Ran(rb0), Outcome::Ran(rb1)) = (a0, a1, b0, b1) else {
        unreachable!()
    };
    let disagree = |what: &str, detail: Json| {
        Verdict::Disagree(json!({"differs": what, "detail": detail, "lean": a0.json(), "cranelift": b0.json()}))
    };
    // How the call ended must not depend on the configuration...
    if ra0.shape() != ra1.shape() || rb0.shape() != rb1.shape() {
        return Verdict::Skip("nondeterministic");
    }
    // ... and must be the same in both engines.
    if ra0.shape() != rb0.shape() {
        return disagree("outcome", json!(null));
    }
    let mut masked = false;
    // Results: the bits stable in both engines.
    for k in 0..ra0.results.len() {
        let m = !(ra0.results[k] ^ ra1.results[k]) & !(rb0.results[k] ^ rb1.results[k]);
        masked |= m != 0xff;
        if ra0.results[k] & m != rb0.results[k] & m {
            return disagree("results", json!({"byte": k, "mask": m}));
        }
    }
    // Memory.
    if ra0.truncated {
        if ra0.hash != ra1.hash || rb0.hash != rb1.hash {
            return Verdict::Skip("nondeterministic (memory)");
        }
        if ra0.hash != rb0.hash {
            return disagree("memory (hash)", json!(null));
        }
    } else {
        let mut addrs: BTreeMap<u64, u64> = BTreeMap::new();
        for r in [ra0, ra1, rb0, rb1] {
            for (&a, &(init, _)) in &r.mem {
                addrs.entry(a).or_insert(init);
            }
        }
        for (&addr, &init) in &addrs {
            let (x0, x1, y0, y1) = (ra0.word(addr, init), ra1.word(addr, init), rb0.word(addr, init), rb1.word(addr, init));
            let m = !(x0 ^ x1) & !(y0 ^ y1);
            masked |= m != !0;
            if x0 & m != y0 & m {
                return disagree(
                    "memory",
                    json!({"address": format!("{addr:#x}"), "initial": format!("{init:#x}"),
                           "lean": format!("{x0:#x}"), "cranelift": format!("{y0:#x}"), "mask": format!("{m:#x}")}),
                );
            }
        }
    }
    Verdict::Agree { class: ra0.class.clone(), masked }
}

/// One harness process: functions `f0..f1`, vectors `v0..v1` (the first function from
/// `vstart`). Returns the records by (fn, vector, config); a process that dies early is
/// restarted after the vector it died in, which gets a `Crash` outcome.
fn run_exe(
    cfg: &DiffConfig,
    exe: &Exe,
    info: &[FnInfo],
    f0: u32,
    f1: u32,
    v0: u32,
    v1: u32,
) -> Result<HashMap<(u32, u32, u32), Outcome>> {
    let mut out = HashMap::new();
    let (mut f, mut vstart) = (f0, v0);
    while f < f1 {
        let mut child = Command::new(&cfg.tools.qemu)
            .arg(&exe.path)
            .args([f.to_string(), f1.to_string(), v0.to_string(), v1.to_string(), vstart.to_string()])
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .with_context(|| format!("running {}", cfg.tools.qemu))?;
        let mut stdout = child.stdout.take().expect("piped");
        let mut stderr_pipe = child.stderr.take().expect("piped");
        let err_reader = std::thread::spawn(move || {
            let mut s = String::new();
            let _ = stderr_pipe.read_to_string(&mut s);
            s
        });
        let started = Instant::now();
        // Watchdog: the per-call timer bounds every call; this bounds a wedged process.
        let limit = Duration::from_secs(600);
        let pid = child.id();
        let (tx, rx) = std::sync::mpsc::channel::<()>();
        let watchdog = std::thread::spawn(move || {
            if rx.recv_timeout(limit).is_err() {
                let _ = Command::new("kill").args(["-9", &pid.to_string()]).status();
            }
        });
        let mut bytes = Vec::new();
        stdout.read_to_end(&mut bytes)?;
        let status = child.wait()?;
        let _ = tx.send(());
        let _ = watchdog.join();
        let stderr = err_reader.join().unwrap_or_default();
        let mut last: Option<(u32, u32, u32)> = None;
        let mut pos = 0;
        while let Some((key, o, len)) = parse_record(exe, info, &bytes[pos..]) {
            out.insert(key, o);
            last = Some(key);
            pos += len;
        }
        // Where the process should have continued.
        let next = match last {
            None => (f, vstart, 0),
            Some((lf, lv, 0)) => (lf, lv, 1),
            Some((lf, lv, _)) => {
                if lv + 1 < v1 {
                    (lf, lv + 1, 0)
                } else {
                    (lf + 1, v0, 0)
                }
            }
        };
        if next.0 >= f1 {
            break;
        }
        if status.success() && pos == bytes.len() {
            // The harness exits 0 only after the last call; a short stream is a bug.
            bail!("{}: harness ended early at {:?}", exe.path.display(), next);
        }
        let why = format!(
            "harness process ended with {status} after {:.1}s{}",
            started.elapsed().as_secs_f64(),
            if stderr.trim().is_empty() { String::new() } else { format!(": {}", stderr.trim()) }
        );
        let (cf, cv, _) = next;
        out.insert((cf, cv, 0), Outcome::Crash(why.clone()));
        out.insert((cf, cv, 1), Outcome::Crash(why));
        if cv + 1 < v1 {
            f = cf;
            vstart = cv + 1;
        } else {
            f = cf + 1;
            vstart = v0;
        }
    }
    Ok(out)
}

#[derive(Default)]
struct FnReport {
    agree: u32,
    /// agreeing vectors where some bits depended on uninitialised memory (not compared)
    masked: u32,
    disagree: u32,
    skipped: BTreeMap<String, u32>,
    outcomes: BTreeMap<String, u32>,
    examples: Vec<Json>,
    vectors: u32,
}

pub fn diff_main(args: &[String]) -> Result<bool> {
    let cfg = parse_diff_args(args)?;
    let dir = match &cfg.keep {
        Some(d) => {
            std::fs::create_dir_all(d)?;
            d.clone()
        }
        None => {
            let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
            let d = std::env::temp_dir().join(format!("clif-native-diff-{}-{nanos}", std::process::id()));
            std::fs::create_dir_all(&d)?;
            d
        }
    };
    let r = diff_in(&cfg, &dir);
    if cfg.keep.is_none() {
        let _ = std::fs::remove_dir_all(&dir);
    }
    r
}

fn compile_c(cfg: &DiffConfig, src: &Path, out: &Path, extra: &[&str]) -> Result<()> {
    let o = run_tool(
        Command::new(&cfg.tools.clang)
            .args([
                "--target=aarch64-linux-gnu",
                "-ffreestanding",
                "-fno-builtin",
                "-nostdlib",
                "-fno-pic",
                "-fno-stack-protector",
                "-mgeneral-regs-only",
                "-O2",
                "-Wall",
                "-Werror",
            ])
            .args(extra)
            .arg("-c")
            .arg(src)
            .arg("-o")
            .arg(out),
        "clang",
    )?;
    if !o.status.success() {
        bail!("compiling {} failed:\n{}", src.display(), String::from_utf8_lossy(&o.stderr));
    }
    Ok(())
}

fn assemble(cfg: &DiffConfig, src: &Path, out: &Path) -> Result<()> {
    let o = run_tool(
        Command::new(&cfg.tools.clang).args(["--target=aarch64-linux-gnu", "-c"]).arg(src).arg("-o").arg(out),
        "clang",
    )?;
    if !o.status.success() {
        bail!("assembling {} failed:\n{}", src.display(), String::from_utf8_lossy(&o.stderr));
    }
    Ok(())
}

fn diff_in(cfg: &DiffConfig, dir: &Path) -> Result<bool> {
    let text = std::fs::read_to_string(&cfg.file).with_context(|| format!("reading {}", cfg.file))?;
    let isa = clif2obj::isa(TRIPLE)?;
    let (data, data_refs) = data_asm(&text, true).with_context(|| format!("{}: data directives", cfg.file))?;
    let test = clif2obj::parse_file(&text, &*isa)?;
    let funcs: Vec<&Function> = test.functions.iter().map(|(f, _)| f).collect();
    let names: Vec<String> = funcs.iter().map(|f| clif2obj::symbol_name(&f.name)).collect::<Result<_>>()?;
    let index: HashMap<String, usize> = names.iter().enumerate().map(|(i, n)| (n.clone(), i)).collect();
    if funcs.is_empty() || funcs.len() > 4095 {
        bail!("{}: {} functions (the harness takes 1..4095)", cfg.file, funcs.len());
    }
    for (f, n) in funcs.iter().zip(&names) {
        let sig = &f.signature;
        if sig.params.len() * SLOT > 256 || sig.returns.len() > 2 || sig.returns.iter().any(|r| r.value_type.bytes() > 16) {
            bail!("%{n}: signature {sig} is outside the harness (at most 16 parameters, 2 results of <= 16 bytes)");
        }
        if let Some(p) = sig.params.iter().find(|p| !matches!(p.purpose, ArgumentPurpose::Normal | ArgumentPurpose::StructReturn)) {
            bail!("%{n}: parameter purpose {} is not supported", p.purpose);
        }
        if sig.params.iter().chain(&sig.returns).any(|p| p.value_type.is_vector() || p.value_type.is_float()) {
            bail!("%{n}: float/vector parameters are not generated");
        }
    }
    let kinds = param_kinds(&funcs, &index);

    // Cranelift: every function, then the trampolines (a separate object for both engines).
    let mut oc = ObjectCompiler::new(isa.clone(), Options::default())?;
    oc.declare(&funcs)?;
    let mut cl_traps: HashMap<String, HashMap<u32, String>> = HashMap::new();
    for (f, n) in funcs.iter().zip(&names) {
        let c = match catch_unwind(AssertUnwindSafe(|| oc.define(f))) {
            Ok(Ok(c)) => c,
            Ok(Err(e)) => bail!("Cranelift cannot compile %{n}: {e:#}"),
            Err(p) => bail!("Cranelift panicked on %{n}: {}", panic_message(p)),
        };
        cl_traps.insert(c.name.clone(), c.traps.iter().map(|t| (t.offset, t.code.clone())).collect());
    }
    let cl_obj = dir.join("cranelift.o");
    std::fs::write(&cl_obj, oc.finish()?)?;
    let tramps: Vec<Function> = funcs
        .iter()
        .enumerate()
        .map(|(k, f)| trampoline(k, &names[k], &f.signature, isa.frontend_config()))
        .collect();
    let mut toc = ObjectCompiler::new(isa.clone(), Options::default())?;
    let trefs: Vec<&Function> = tramps.iter().collect();
    toc.declare(&trefs)?;
    let mut tramp_names = Vec::new();
    for t in &tramps {
        tramp_names.push(toc.define(t).context("compiling a trampoline")?.name);
    }
    let tramp_obj = dir.join("tramps.o");
    std::fs::write(&tramp_obj, toc.finish()?)?;

    let lean = read_table(&cfg.lean_table)?;
    let mut lean_traps: HashMap<String, HashMap<u32, String>> =
        lean.functions.iter().map(|(n, _, t)| (n.clone(), t.clone())).collect();
    if let Some(n) = names.iter().find(|n| !lean_traps.contains_key(*n)) {
        let why = lean.unsupported.get(n).cloned().unwrap_or_default();
        bail!("%{n} is not in the Lean object ({why})");
    }
    // The lean engine's objects: the Lean object, or (`--lean-only`) the Lean object and the
    // Cranelift object with the other engine's copies of each function weakened.
    let mut lean_objs = vec![cfg.lean_obj.clone()];
    if !cfg.lean_only.is_empty() {
        let objcopy = std::env::var("CLIF_NATIVE_OBJCOPY").unwrap_or_else(|_| "llvm-objcopy-18".into());
        let weaken = |src: &Path, dst: &Path, keep: &dyn Fn(&str) -> bool| -> Result<()> {
            let mut c = Command::new(&objcopy);
            for n in names.iter().filter(|n| !keep(n)) {
                c.arg(format!("--weaken-symbol={n}"));
            }
            let o = run_tool(c.arg(src).arg(dst), "llvm-objcopy")?;
            if !o.status.success() {
                bail!("llvm-objcopy failed:\n{}", String::from_utf8_lossy(&o.stderr));
            }
            Ok(())
        };
        let sel: HashSet<&str> = cfg.lean_only.iter().map(String::as_str).collect();
        if let Some(n) = sel.iter().find(|n| !index.contains_key(**n)) {
            bail!("--lean-only {n}: no such function");
        }
        let (lo, co) = (dir.join("lean-part.o"), dir.join("cranelift-part.o"));
        weaken(&cfg.lean_obj, &lo, &|n| sel.contains(n))?;
        weaken(&cl_obj, &co, &|n| !sel.contains(n))?;
        lean_objs = vec![lo, co];
        for n in &names {
            if !sel.contains(n.as_str()) {
                lean_traps.insert(n.clone(), cl_traps[n].clone());
            }
        }
    }

    // The data objects at fixed addresses; their pointers to the file's functions point at
    // the functions' thunks instead (vtables etc. then hold the same values in both
    // executables).
    let data_o = match &data {
        Some(asm) => {
            let asm: String = asm
                .lines()
                .map(|l| {
                    let Some(item) = l.strip_prefix(".quad ") else { return format!("{l}\n") };
                    let at = item.rfind(['+', '-']).unwrap_or(item.len());
                    match index.get(&item[..at]) {
                        Some(k) => format!(".quad clifdiff_thunk_{k}{}\n", &item[at..]),
                        None => format!("{l}\n"),
                    }
                })
                .collect();
            let s = dir.join("data.s");
            std::fs::write(&s, asm)?;
            let o = dir.join("data.o");
            assemble(cfg, &s, &o)?;
            Some(o)
        }
        None => None,
    };
    let mut data_names: Vec<&String> = data_refs.keys().collect();
    data_names.sort();

    // The harness tables.
    use std::fmt::Write as _;
    let mut h = String::new();
    let only: HashSet<&str> = cfg.only.iter().map(String::as_str).collect();
    writeln!(h, "#define CLIFDIFF_NFNS {}", funcs.len()).unwrap();
    writeln!(h, "#define CLIFDIFF_NDATA {}", data_names.len()).unwrap();
    writeln!(h, "#define CLIFDIFF_SEED {}UL", cfg.seed).unwrap();
    writeln!(h, "#define CLIFDIFF_TIMEOUT_US {}UL", cfg.call_timeout_us).unwrap();
    let mut cands: Vec<Vec<usize>> = Vec::new();
    for (k, t) in tramp_names.iter().enumerate() {
        writeln!(h, "extern void clifdiff_tramp_{k}(void *) __asm__(\"{}\");", c_string(t)).unwrap();
        writeln!(h, "extern const u8 clifdiff_code_{k}[] __asm__(\"{}\");", c_string(&names[k])).unwrap();
        let pd: Vec<String> = funcs[k]
            .signature
            .params
            .iter()
            .zip(&kinds[k])
            .flat_map(|(p, (kd, sg))| {
                // kind 3: the candidate list of the functions with the called signature
                let cand = match sg {
                    Some(sg) => {
                        let fs: Vec<usize> = (0..funcs.len()).filter(|&g| &funcs[g].signature.to_string() == sg).collect();
                        let at = cands.len();
                        cands.push(fs);
                        at + 1
                    }
                    None => 0,
                };
                [p.value_type.bytes().to_string(), kd.to_string(), (cand & 0xff).to_string(), (cand >> 8).to_string()]
            })
            .collect();
        writeln!(h, "static const u8 clifdiff_pdesc_{k}[] = {{{}}};", if pd.is_empty() { "0".into() } else { pd.join(",") })
            .unwrap();
    }
    for (k, d) in data_names.iter().enumerate() {
        writeln!(h, "extern const u8 clifdiff_datum_{k}[] __asm__(\"{}\");", c_string(d)).unwrap();
    }
    writeln!(h, "static const struct clifdiff_fn clifdiff_fns[] = {{").unwrap();
    for (k, f) in funcs.iter().enumerate() {
        writeln!(
            h,
            "  {{clifdiff_tramp_{k}, clifdiff_code_{k}, {}, {}, clifdiff_pdesc_{k}}},",
            f.signature.params.len(),
            f.signature.returns.len()
        )
        .unwrap();
    }
    writeln!(h, "}};").unwrap();
    for (k, c) in cands.iter().enumerate() {
        let items: Vec<String> = std::iter::once(c.len()).chain(c.iter().copied()).map(|x| x.to_string()).collect();
        writeln!(h, "static const unsigned short clifdiff_cand_{k}[] = {{{}}};", items.join(",")).unwrap();
    }
    let cl: Vec<String> = std::iter::once("0".to_string()).chain((0..cands.len()).map(|k| format!("clifdiff_cand_{k}"))).collect();
    writeln!(h, "static const unsigned short *const clifdiff_cands[] = {{{}}};", cl.join(",")).unwrap();
    let dl: Vec<String> = (0..data_names.len()).map(|k| format!("clifdiff_datum_{k}")).collect();
    writeln!(h, "static const u8 *const clifdiff_data[] = {{{}}};", if dl.is_empty() { "0".into() } else { dl.join(",") })
        .unwrap();
    // The data objects that point at functions of the file (vtables): kind-4 parameters.
    let vt: Vec<String> = data_names
        .iter()
        .enumerate()
        .filter(|(_, d)| data_refs[d.as_str()].iter().any(|r| index.contains_key(r)))
        .map(|(k, _)| format!("clifdiff_datum_{k}"))
        .collect();
    writeln!(h, "#define CLIFDIFF_NVTABLES {}", vt.len()).unwrap();
    writeln!(h, "static const u8 *const clifdiff_vtables[] = {{{}}};", if vt.is_empty() { "0".into() } else { vt.join(",") })
        .unwrap();
    std::fs::write(dir.join("clifdiff_tables.h"), h)?;
    std::fs::write(dir.join("diffharness.c"), DIFF_HARNESS_C)?;
    let harness_o = dir.join("diffharness.o");
    compile_c(cfg, &dir.join("diffharness.c"), &harness_o, &[])?;

    // Undefined symbols -> aliases, dead data addresses, trapping stubs.
    let mut defined: HashSet<String> = HashSet::new();
    let mut undefined: HashSet<String> = HashSet::new();
    let mut objs: Vec<PathBuf> = vec![harness_o.clone(), tramp_obj.clone(), cl_obj.clone(), cfg.lean_obj.clone()];
    objs.extend(data_o.iter().cloned());
    objs.extend(cfg.links.iter().cloned());
    for o in &objs {
        let (d, u) = object_symbols(o)?;
        undefined.extend(u);
        if o != &cl_obj && o != &cfg.lean_obj {
            defined.extend(d);
        }
    }
    defined.extend(names.iter().cloned());
    defined.insert("clifdiff_thunks".to_string());
    defined.extend((0..names.len()).map(|k| format!("clifdiff_thunk_{k}")));
    let mut undef: Vec<String> = undefined.into_iter().filter(|s| !defined.contains(s)).collect();
    undef.sort();
    let called: HashSet<String> = funcs.iter().flat_map(|f| clif2obj::callees(f).unwrap_or_default()).collect();
    // In their own section at a fixed address: stub addresses do not depend on the engine.
    let mut stubs = String::from(".section clifd_stubs,\"ax\",@progbits\n");
    let mut dead = 0u64;
    let mut stub_report = Vec::new();
    let mut trap_stubs: HashSet<String> = HashSet::new();
    for s in &undef {
        let alias = cfg.aliases.get(s).cloned().or_else(|| {
            ALLOCATOR.iter().find(|(suffix, _)| s == suffix || s.ends_with(&format!("_{suffix}"))).map(|(_, t)| t.to_string())
        });
        if let Some(t) = alias {
            writeln!(stubs, ".globl {s}\n.p2align 2\n{s}:\n  adrp x16, {t}\n  add x16, x16, :lo12:{t}\n  br x16").unwrap();
            stub_report.push(json!({"symbol": s, "alias": t}));
        } else if !called.contains(s) {
            writeln!(stubs, ".globl {s}\n.set {s}, {:#x}", DEAD_DATA_ADDR + 64 * dead).unwrap();
            dead += 1;
            stub_report.push(json!({"symbol": s, "dead_data": true}));
        } else {
            writeln!(stubs, ".globl {s}\n.p2align 2\n.type {s}, %function\n{s}:\n  udf #251\n.size {s}, 4").unwrap();
            stub_report.push(json!({"symbol": s, "trap_stub": true}));
            trap_stubs.insert(s.clone());
        }
    }
    let mut thunks = String::from(".section clifd_thunks,\"ax\",@progbits\n.globl clifdiff_thunks\nclifdiff_thunks:\n");
    // A thunk loads its target from `clifdiff_fnptrs` (another fixed-address section), so the
    // thunks' own bytes, which a call may read through a pointer, are engine-independent.
    for k in 0..names.len() {
        writeln!(
            thunks,
            ".p2align 4\n.globl clifdiff_thunk_{k}\nclifdiff_thunk_{k}:\n  adrp x16, clifdiff_fnptrs\n  \
             add x16, x16, :lo12:clifdiff_fnptrs\n  ldr x16, [x16, #{}]\n  br x16",
            8 * k
        )
        .unwrap();
    }
    thunks.push_str(".section clifd_fnptrs,\"a\",@progbits\n.p2align 3\nclifdiff_fnptrs:\n");
    for n in &names {
        writeln!(thunks, "  .quad {n}").unwrap();
    }
    let thunks_s = dir.join("thunks.s");
    std::fs::write(&thunks_s, thunks)?;
    let thunks_o = dir.join("thunks.o");
    assemble(cfg, &thunks_s, &thunks_o)?;
    let stubs_s = dir.join("stubs.s");
    std::fs::write(&stubs_s, stubs)?;
    let stubs_o = dir.join("stubs.o");
    assemble(cfg, &stubs_s, &stubs_o)?;

    // The usual layout (one 64 KiB-aligned segment per permission), then the data objects at
    // fixed addresses: the engines' code sizes differ, the observable data addresses do not.
    let script = dir.join("link.ld");
    std::fs::write(
        &script,
        format!(
            "SECTIONS {{\n  . = 0x210000;\n  .text : {{ *(.text .text.*) }}\n  . = ALIGN(0x10000);\n  \
             .rodata : {{ *(.rodata .rodata.*) }}\n  . = ALIGN(0x10000);\n  .data : {{ *(.data .data.*) }}\n  \
             .got : {{ *(.got .got.*) }}\n  .bss : {{ *(.bss .bss.* COMMON) }}\n  \
             . = {RO_ADDR:#x};\n  clifd_ro : {{ *(clifd_ro) }}\n  \
             . = {RW_ADDR:#x};\n  clifd_rw : {{ *(clifd_rw) }}\n  \
             . = {THUNK_ADDR:#x};\n  clifd_thunks : {{ *(clifd_thunks) }}\n  \
             . = {STUB_ADDR:#x};\n  clifd_stubs : {{ *(clifd_stubs) }}\n  \
             . = {FNPTR_ADDR:#x};\n  clifd_fnptrs : {{ *(clifd_fnptrs) }}\n}}\n"
        ),
    )?;
    let link = |engine_objs: &[PathBuf], out: &Path| -> Result<()> {
        let mut l = Command::new(&cfg.tools.lld);
        l.args(["-flavor", "gnu", "-static", "--no-demangle", "-e", "_start", "-T"])
            .arg(&script)
            .arg("-o")
            .arg(out)
            .arg(&harness_o)
            .arg(&tramp_obj);
        if let Some(o) = &data_o {
            l.arg(o);
        }
        l.args(engine_objs).arg(&stubs_o).arg(&thunks_o).args(&cfg.links);
        let o = run_tool(&mut l, "rust-lld")?;
        if !o.status.success() {
            bail!("linking {} failed:\n{}", out.display(), String::from_utf8_lossy(&o.stderr));
        }
        Ok(())
    };
    let lean_exe = dir.join("lean.exe");
    let cl_exe = dir.join("cranelift.exe");
    link(&lean_objs, &lean_exe)?;
    link(std::slice::from_ref(&cl_obj), &cl_exe)?;
    let engines = [Exe::load(lean_exe, lean_traps, trap_stubs.clone())?, Exe::load(cl_exe, cl_traps, trap_stubs)?];

    let info: Vec<FnInfo> = funcs
        .iter()
        .zip(&names)
        .map(|(f, n)| FnInfo {
            name: n.clone(),
            ret_bytes: f
                .signature
                .returns
                .iter()
                .enumerate()
                .map(|(j, r): (usize, &cranelift_codegen::ir::AbiParam)| {
                    let t: Type = r.value_type;
                    (j * SLOT, j * SLOT + t.bytes() as usize)
                })
                .collect(),
        })
        .collect();

    // Rounds of vectors: [0, vectors), then more for the functions short of min_vectors.
    let selected: Vec<u32> =
        (0..funcs.len() as u32).filter(|&i| only.is_empty() || only.contains(names[i as usize].as_str())).collect();
    let mut reports: HashMap<u32, FnReport> = selected.iter().map(|&i| (i, FnReport::default())).collect();
    let mut todo: Vec<u32> = selected.clone();
    let (mut lo, mut hi) = (0u32, cfg.vectors);
    while !todo.is_empty() && lo < hi {
        // Jobs: contiguous function ranges per engine, the vector range [lo, hi).
        let chunk = todo.len().div_ceil(cfg.jobs.max(1)).max(1);
        let mut jobs: Vec<(usize, Vec<u32>)> = Vec::new();
        for part in todo.chunks(chunk) {
            for e in 0..2 {
                jobs.push((e, part.to_vec()));
            }
        }
        let queue = Mutex::new(jobs);
        let results: Mutex<[HashMap<(u32, u32, u32), Outcome>; 2]> = Mutex::new([HashMap::new(), HashMap::new()]);
        let errors: Mutex<Vec<anyhow::Error>> = Mutex::new(Vec::new());
        std::thread::scope(|s| {
            for _ in 0..cfg.jobs.max(1) * 2 {
                s.spawn(|| {
                    loop {
                        let Some((e, fs)) = queue.lock().pop() else { break };
                        // consecutive runs of function indices in one process each
                        let mut i = 0;
                        while i < fs.len() {
                            let mut j = i + 1;
                            while j < fs.len() && fs[j] == fs[j - 1] + 1 {
                                j += 1;
                            }
                            match run_exe(cfg, &engines[e], &info, fs[i], fs[j - 1] + 1, lo, hi) {
                                Ok(r) => results.lock()[e].extend(r),
                                Err(err) => errors.lock().push(err),
                            }
                            i = j;
                        }
                    }
                });
            }
        });
        if let Some(e) = errors.into_inner().pop() {
            return Err(e);
        }
        let [a, b] = results.into_inner();
        for &f in &todo {
            let rep = reports.get_mut(&f).unwrap();
            for v in lo..hi {
                rep.vectors += 1;
                let get = |m: &HashMap<(u32, u32, u32), Outcome>, c| {
                    m.get(&(f, v, c)).cloned().unwrap_or(Outcome::Crash("no record".into()))
                };
                let (a0, a1, b0, b1) = (get(&a, 0), get(&a, 1), get(&b, 0), get(&b, 1));
                match compare(&a0, &a1, &b0, &b1) {
                    Verdict::Skip(why) => {
                        *rep.skipped.entry(why.to_string()).or_default() += 1;
                        if rep.examples.len() < 3 && why == "crash" {
                            rep.examples.push(json!({"vector": v, "skipped": why, "lean": a0.json(), "cranelift": b0.json()}));
                        }
                    }
                    Verdict::Agree { class, masked } => {
                        rep.agree += 1;
                        rep.masked += u32::from(masked);
                        *rep.outcomes.entry(class).or_default() += 1;
                    }
                    Verdict::Disagree(detail) => {
                        rep.disagree += 1;
                        if rep.examples.len() < 5 {
                            rep.examples.push(json!({"vector": v, "disagreement": detail}));
                        }
                    }
                }
            }
        }
        todo.retain(|f| {
            let r = &reports[f];
            r.agree + r.disagree < cfg.min_vectors
        });
        lo = hi;
        hi = (hi + cfg.vectors).min(cfg.max_vectors);
    }

    let mut total = json!({"functions": 0, "vectors": 0, "agree": 0, "agree_masked": 0, "disagree": 0, "below_min": 0});
    let mut skipped_total: BTreeMap<String, u64> = BTreeMap::new();
    let mut ok = true;
    for &f in &selected {
        let r = &reports[&f];
        let fi = &info[f as usize];
        let rec = json!({
            "func": fi.name,
            "params": kinds[f as usize].iter().map(|k| k.0).collect::<Vec<_>>(),
            "vectors": r.vectors,
            "agree": r.agree,
            "agree_masked": r.masked,
            "disagree": r.disagree,
            "skipped": r.skipped,
            "outcomes": r.outcomes,
            "examples": r.examples,
        });
        println!("{rec}");
        ok &= r.disagree == 0;
        total["functions"] = json!(total["functions"].as_u64().unwrap() + 1);
        total["vectors"] = json!(total["vectors"].as_u64().unwrap() + u64::from(r.vectors));
        total["agree"] = json!(total["agree"].as_u64().unwrap() + u64::from(r.agree));
        total["disagree"] = json!(total["disagree"].as_u64().unwrap() + u64::from(r.disagree));
        total["agree_masked"] = json!(total["agree_masked"].as_u64().unwrap() + u64::from(r.masked));
        if r.agree + r.disagree < cfg.min_vectors {
            total["below_min"] = json!(total["below_min"].as_u64().unwrap() + 1);
        }
        for (k, n) in &r.skipped {
            *skipped_total.entry(k.clone()).or_default() += u64::from(*n);
        }
    }
    total["skipped"] = json!(skipped_total);
    total["externs"] = json!(stub_report);
    total["file"] = json!(cfg.file);
    println!("{}", json!({ "summary": total }));
    Ok(ok)
}
