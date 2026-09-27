//! `lean-regalloc [IN.json|-] [OUT.json|-]` (default: stdin, stdout).
//!
//! The Lean backend's register-allocation oracle. It reads VCode (blocks, CFG, block
//! parameters, branch arguments, operands with regalloc2 constraints, clobbers) and the
//! machine environment as JSON, runs `regalloc2::run` (0.15.2, unchanged) with the options
//! Cranelift 0.136.1 uses (`machinst/compile.rs`: backtracking = `Algorithm::Ion`,
//! `verbose_log` off, `validate_ssa` on as in Cranelift's debug builds), runs regalloc2's own
//! symbolic checker (`regalloc2::checker`, Cranelift's `regalloc_checker`) as an extra
//! cross-check, and writes the allocations, edits and spill-slot count as JSON.
//!
//! This program is *untrusted*: the Lean checker (`FV/Backend/RegallocCheck.lean`) validates
//! every allocation independently. The JSON schema is in `docs/contracts/regalloc.md`.
//!
//! Exit status: 0 when the output was written (per-function allocation failures are reported
//! inside it), 1 on unreadable/malformed input, 2 on bad usage.

use regalloc2::checker::Checker;
use regalloc2::{
    Algorithm, Allocation, AllocationKind, Block, Edit, Function, Inst, InstPosition, InstRange,
    MachineEnv, Operand, OperandConstraint, OperandKind, OperandPos, Output, PReg, PRegSet,
    RegClass, RegallocOptions, VReg,
};
use serde_json::{Value, json};
use std::io::{Read, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

/// One VCode function, implementing `regalloc2::Function`.
struct Func {
    name: String,
    entry: Block,
    classes: Vec<RegClass>,
    blocks: Vec<BlockData>,
    insts: Vec<InstData>,
}

struct BlockData {
    insts: InstRange,
    succs: Vec<Block>,
    preds: Vec<Block>,
    params: Vec<VReg>,
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum InstKind {
    Ret,
    Branch,
    Other,
}

struct InstData {
    ops: Vec<Operand>,
    clobbers: PRegSet,
    kind: InstKind,
    /// Branch arguments, one list per successor of the block.
    args: Vec<Vec<VReg>>,
}

impl Function for Func {
    fn num_insts(&self) -> usize {
        self.insts.len()
    }
    fn num_blocks(&self) -> usize {
        self.blocks.len()
    }
    fn entry_block(&self) -> Block {
        self.entry
    }
    fn block_insns(&self, block: Block) -> InstRange {
        self.blocks[block.index()].insts
    }
    fn block_succs(&self, block: Block) -> &[Block] {
        &self.blocks[block.index()].succs
    }
    fn block_preds(&self, block: Block) -> &[Block] {
        &self.blocks[block.index()].preds
    }
    fn block_params(&self, block: Block) -> &[VReg] {
        &self.blocks[block.index()].params
    }
    fn is_ret(&self, insn: Inst) -> bool {
        self.insts[insn.index()].kind == InstKind::Ret
    }
    fn is_branch(&self, insn: Inst) -> bool {
        self.insts[insn.index()].kind == InstKind::Branch
    }
    fn branch_blockparams(&self, _block: Block, insn: Inst, succ_idx: usize) -> &[VReg] {
        &self.insts[insn.index()].args[succ_idx]
    }
    fn inst_operands(&self, insn: Inst) -> &[Operand] {
        &self.insts[insn.index()].ops
    }
    fn inst_clobbers(&self, insn: Inst) -> PRegSet {
        self.insts[insn.index()].clobbers
    }
    fn num_vregs(&self) -> usize {
        self.classes.len()
    }
    /// Cranelift aarch64 `get_number_of_spillslots_for_value`: 8-byte slots; int = 1,
    /// float/vector (128-bit registers) = 2.
    fn spillslot_size(&self, regclass: RegClass) -> usize {
        match regclass {
            RegClass::Int => 1,
            RegClass::Float | RegClass::Vector => 2,
        }
    }
    /// Cranelift's `VCode` returns `true`.
    fn allow_multiple_vreg_defs(&self) -> bool {
        true
    }
}

type R<T> = Result<T, String>;

fn field<'a>(v: &'a Value, k: &str) -> R<&'a Value> {
    v.get(k).ok_or_else(|| format!("missing field `{k}`"))
}

fn arr<'a>(v: &'a Value, what: &str) -> R<&'a Vec<Value>> {
    v.as_array().ok_or_else(|| format!("`{what}` is not an array"))
}

fn num(v: &Value, what: &str) -> R<usize> {
    v.as_u64()
        .map(|n| n as usize)
        .ok_or_else(|| format!("`{what}` is not a natural number"))
}

fn string<'a>(v: &'a Value, what: &str) -> R<&'a str> {
    v.as_str().ok_or_else(|| format!("`{what}` is not a string"))
}

/// `"x3"` (integer class, hardware encoding 3) or `"v17"` (float class).
fn preg(s: &str) -> R<PReg> {
    let (class, rest) = if let Some(r) = s.strip_prefix('x') {
        (RegClass::Int, r)
    } else if let Some(r) = s.strip_prefix('v') {
        (RegClass::Float, r)
    } else {
        return Err(format!("bad physical register `{s}`"));
    };
    let n: usize = rest.parse().map_err(|_| format!("bad physical register `{s}`"))?;
    if n >= PReg::MAX + 1 {
        return Err(format!("physical register `{s}` out of range"));
    }
    Ok(PReg::new(n, class))
}

fn preg_name(p: PReg) -> String {
    match p.class() {
        RegClass::Int => format!("x{}", p.hw_enc()),
        RegClass::Float => format!("v{}", p.hw_enc()),
        RegClass::Vector => format!("q{}", p.hw_enc()),
    }
}

fn alloc_name(a: Allocation) -> String {
    match a.kind() {
        AllocationKind::None => "none".to_string(),
        AllocationKind::Reg => preg_name(a.as_reg().unwrap()),
        AllocationKind::Stack => format!("s{}", a.as_stack().unwrap().index()),
    }
}

fn preg_set(v: &Value, what: &str) -> R<PRegSet> {
    let mut s = PRegSet::empty();
    for r in arr(v, what)? {
        s.add(preg(string(r, what)?)?);
    }
    Ok(s)
}

fn parse_env(v: &Value) -> R<MachineEnv> {
    let classes = |k: &str| -> R<[PRegSet; 3]> {
        let a = arr(field(v, k)?, k)?;
        if a.len() != 3 {
            return Err(format!("`{k}` must have 3 classes (int, float, vector)"));
        }
        Ok([
            preg_set(&a[0], k)?,
            preg_set(&a[1], k)?,
            preg_set(&a[2], k)?,
        ])
    };
    let scratch_v = arr(field(v, "scratch")?, "scratch")?;
    if scratch_v.len() != 3 {
        return Err("`scratch` must have 3 entries".into());
    }
    let mut scratch = [None, None, None];
    for (i, s) in scratch_v.iter().enumerate() {
        if !s.is_null() {
            scratch[i] = Some(preg(string(s, "scratch")?)?);
        }
    }
    let fixed_stack_slots = arr(field(v, "fixed_stack")?, "fixed_stack")?
        .iter()
        .map(|r| preg(string(r, "fixed_stack")?))
        .collect::<R<Vec<_>>>()?;
    Ok(MachineEnv {
        preferred_regs_by_class: classes("preferred")?,
        non_preferred_regs_by_class: classes("non_preferred")?,
        scratch_by_class: scratch,
        fixed_stack_slots,
    })
}

fn parse_operand(v: &Value, classes: &[RegClass]) -> R<Operand> {
    let vi = num(field(v, "v")?, "v")?;
    let class = *classes
        .get(vi)
        .ok_or_else(|| format!("operand vreg {vi} out of range"))?;
    let vreg = VReg::new(vi, class);
    let kind = match string(field(v, "k")?, "k")? {
        "use" => OperandKind::Use,
        "def" => OperandKind::Def,
        k => return Err(format!("bad operand kind `{k}`")),
    };
    let pos = match string(field(v, "p")?, "p")? {
        "early" => OperandPos::Early,
        "late" => OperandPos::Late,
        p => return Err(format!("bad operand position `{p}`")),
    };
    let c = string(field(v, "c")?, "c")?;
    let constraint = if c == "reg" {
        OperandConstraint::Reg
    } else if c == "any" {
        OperandConstraint::Any
    } else if c == "stack" {
        OperandConstraint::Stack
    } else if let Some(r) = c.strip_prefix("fixed:") {
        OperandConstraint::FixedReg(preg(r)?)
    } else if let Some(i) = c.strip_prefix("reuse:") {
        OperandConstraint::Reuse(i.parse().map_err(|_| format!("bad constraint `{c}`"))?)
    } else {
        return Err(format!("bad constraint `{c}`"));
    };
    Ok(Operand::new(vreg, constraint, kind, pos))
}

fn parse_func(v: &Value) -> R<Func> {
    let name = string(field(v, "name")?, "name")?.to_string();
    let classes = string(field(v, "vregs")?, "vregs")?
        .chars()
        .map(|c| match c {
            'i' => Ok(RegClass::Int),
            'f' => Ok(RegClass::Float),
            _ => Err(format!("bad vreg class `{c}`")),
        })
        .collect::<R<Vec<_>>>()?;
    let vreg = |x: &Value, what: &str| -> R<VReg> {
        let i = num(x, what)?;
        let c = *classes
            .get(i)
            .ok_or_else(|| format!("{what}: vreg {i} out of range"))?;
        Ok(VReg::new(i, c))
    };
    let nblocks = arr(field(v, "blocks")?, "blocks")?.len();
    let block = |x: &Value, what: &str| -> R<Block> {
        let i = num(x, what)?;
        if i >= nblocks {
            return Err(format!("{what}: block {i} out of range"));
        }
        Ok(Block::new(i))
    };
    let mut blocks = vec![];
    for b in arr(field(v, "blocks")?, "blocks")? {
        let r = arr(field(b, "insts")?, "insts")?;
        if r.len() != 2 {
            return Err("block `insts` must be [start, end)".into());
        }
        let (s, e) = (num(&r[0], "insts")?, num(&r[1], "insts")?);
        if s >= e {
            return Err("empty block".into());
        }
        blocks.push(BlockData {
            insts: InstRange::new(Inst::new(s), Inst::new(e)),
            succs: arr(field(b, "succs")?, "succs")?
                .iter()
                .map(|x| block(x, "succs"))
                .collect::<R<_>>()?,
            preds: arr(field(b, "preds")?, "preds")?
                .iter()
                .map(|x| block(x, "preds"))
                .collect::<R<_>>()?,
            params: arr(field(b, "params")?, "params")?
                .iter()
                .map(|x| vreg(x, "params"))
                .collect::<R<_>>()?,
        });
    }
    let mut insts = vec![];
    for i in arr(field(v, "insts")?, "insts")? {
        let ops = arr(field(i, "ops")?, "ops")?
            .iter()
            .map(|o| parse_operand(o, &classes))
            .collect::<R<Vec<_>>>()?;
        let clobbers = match i.get("clobbers") {
            Some(c) => preg_set(c, "clobbers")?,
            None => PRegSet::empty(),
        };
        let kind = match i.get("kind").map(|k| string(k, "kind")).transpose()? {
            Some("ret") => InstKind::Ret,
            Some("branch") => InstKind::Branch,
            Some("other") | None => InstKind::Other,
            Some(k) => return Err(format!("bad instruction kind `{k}`")),
        };
        let args = match i.get("args") {
            Some(a) => arr(a, "args")?
                .iter()
                .map(|l| {
                    arr(l, "args")?
                        .iter()
                        .map(|x| vreg(x, "args"))
                        .collect::<R<Vec<_>>>()
                })
                .collect::<R<Vec<_>>>()?,
            None => vec![],
        };
        insts.push(InstData {
            ops,
            clobbers,
            kind,
            args,
        });
    }
    // Structural checks regalloc2 would otherwise hit as index panics.
    for (bi, b) in blocks.iter().enumerate() {
        if b.insts.last().index() >= insts.len() {
            return Err(format!("block {bi}: instruction range out of bounds"));
        }
        let last = &insts[b.insts.last().index()];
        if last.kind == InstKind::Branch && last.args.len() != b.succs.len() {
            return Err(format!(
                "block {bi}: branch has {} argument lists for {} successors",
                last.args.len(),
                b.succs.len()
            ));
        }
    }
    let entry = block(field(v, "entry")?, "entry")?;
    Ok(Func {
        name,
        entry,
        classes,
        blocks,
        insts,
    })
}

/// Cranelift 0.136.1 `machinst/compile.rs`: default options, `algorithm` from the default
/// `regalloc_algorithm = "backtracking"` (= `Ion`), `verbose_log` from the default
/// `regalloc_verbose_logs = false`, `validate_ssa = true` as under `debug_assertions`.
fn options() -> RegallocOptions {
    let mut o = RegallocOptions::default();
    o.verbose_log = false;
    o.validate_ssa = true;
    o.algorithm = Algorithm::Ion;
    o
}

fn output_json(f: &Func, out: &Output, checker: &str) -> Value {
    let allocs: Vec<Value> = (0..f.insts.len())
        .map(|i| {
            Value::Array(
                out.inst_allocs(Inst::new(i))
                    .iter()
                    .map(|a| Value::String(alloc_name(*a)))
                    .collect(),
            )
        })
        .collect();
    let edits: Vec<Value> = out
        .edits
        .iter()
        .map(|(pt, e)| {
            let Edit::Move { from, to } = e;
            json!({
                "inst": pt.inst().index(),
                "pos": match pt.pos() { InstPosition::Before => "before", InstPosition::After => "after" },
                "from": alloc_name(*from),
                "to": alloc_name(*to),
            })
        })
        .collect();
    json!({
        "name": f.name,
        "ok": true,
        "num_spillslots": out.num_spillslots,
        "allocs": allocs,
        "edits": edits,
        "checker": checker,
        "stats": format!("{:?}", out.stats),
    })
}

fn alloc_one(v: &Value, env: &MachineEnv) -> Value {
    let name = v.get("name").and_then(|n| n.as_str()).unwrap_or("?").to_string();
    let f = match parse_func(v) {
        Ok(f) => f,
        Err(e) => return json!({"name": name, "ok": false, "error": format!("bad input: {e}")}),
    };
    let res = catch_unwind(AssertUnwindSafe(|| {
        let out = regalloc2::run(&f, env, &options()).map_err(|e| format!("regalloc2: {e:?}"))?;
        let mut checker = Checker::new(&f, env);
        checker.prepare(&out);
        let verdict = match checker.run() {
            Ok(()) => "ok".to_string(),
            Err(e) => format!("{e:?}"),
        };
        Ok::<_, String>((out, verdict))
    }));
    match res {
        Ok(Ok((out, verdict))) => output_json(&f, &out, &verdict),
        Ok(Err(e)) => json!({"name": name, "ok": false, "error": e}),
        Err(p) => {
            let msg = p
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "unknown panic".into());
            json!({"name": name, "ok": false, "error": format!("regalloc2 panicked: {msg}")})
        }
    }
}

fn run(input: &str) -> R<String> {
    let v: Value = serde_json::from_str(input).map_err(|e| format!("input is not JSON: {e}"))?;
    let env = parse_env(field(&v, "env")?)?;
    let funcs: Vec<Value> = arr(field(&v, "functions")?, "functions")?
        .iter()
        .map(|f| alloc_one(f, &env))
        .collect();
    Ok(serde_json::to_string(&json!({ "functions": funcs })).unwrap() + "\n")
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() > 2 || args.iter().any(|a| a == "-h" || a == "--help") {
        eprintln!("usage: lean-regalloc [IN.json|-] [OUT.json|-]");
        std::process::exit(2);
    }
    let input_path = args.first().map(String::as_str).unwrap_or("-");
    let output_path = args.get(1).map(String::as_str).unwrap_or("-");
    let mut input = String::new();
    let read = if input_path == "-" {
        std::io::stdin().read_to_string(&mut input).map(|_| ())
    } else {
        std::fs::read_to_string(input_path).map(|s| input = s)
    };
    if let Err(e) = read {
        eprintln!("lean-regalloc: cannot read {input_path}: {e}");
        std::process::exit(1);
    }
    let out = match run(&input) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("lean-regalloc: {e}");
            std::process::exit(1);
        }
    };
    let written = if output_path == "-" {
        std::io::stdout().write_all(out.as_bytes())
    } else {
        std::fs::write(output_path, out)
    };
    if let Err(e) = written {
        eprintln!("lean-regalloc: cannot write {output_path}: {e}");
        std::process::exit(1);
    }
}
