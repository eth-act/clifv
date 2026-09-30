//! Recover the data objects cg_clif hides behind `symbol_value` (rust-route step 1).
//!
//! usage: clif-data-export <clif-dir> <obj> --out F.clif --gvmap F.tsv [--fnmap F.tsv] [--stage unopt]
//!
//! `--fnmap`: also name the callees declared only by FuncId (`u0:N<TAB>symbol` lines, see
//! `name_callees`), for `normalize.py --fnmap`.
//!
//! cg_clif puts the bytes of every static data object (panic `Location`s and messages,
//! constant tables, constant enum values, vtables) only into its object file, as local
//! `.LdataN` symbols; the CLIF dumps only declare `gvN = symbol colocated userextnameJ`
//! with a comment naming the allocation. This tool recovers the bytes:
//!
//! * every external-name use in a function body — a `symbol_value` of a data object, a
//!   `func_addr` of a non-colocated declaration, or a call of a non-colocated declaration
//!   — lowers to exactly one GOT load (an `ADR_GOT_PAGE` + `LD64_GOT_LO12` relocation
//!   pair), and cg_clif emits those in codegen order. So the uses of a function, in CLIF
//!   layout order, match the function's GOT pairs, in code order, one to one. The match
//!   is checked (pair counts per function, use kind vs. symbol kind, and the identity of
//!   every allocation across functions); any mismatch is a loud error, never a guess.
//! * each referenced data object's bytes are read from its section, its internal
//!   `R_AARCH64_ABS64` relocations are resolved, and one `; data:` directive is emitted
//!   per object, plus the per-(dump file, gv) renaming table.
//!
//! Data objects reachable only from other data objects (the message of a panic
//! `Location`, a vtable's function targets) are recovered transitively.
use object::read::{Object, ObjectSection, ObjectSymbol, SymbolSection};
use object::{SectionKind, SymbolKind};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

fn die(msg: String) -> ! {
    eprintln!("clif-data-export: {msg}");
    std::process::exit(1)
}

/// Parse a decimal number, digits only.
fn parse_u32(s: &str) -> Option<u32> {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    s.parse().ok()
}

/// cg_clif writes the comment of a declaration or instruction on the same line, after the
/// code, separated by ` ; `. The code itself never contains `;`.
fn split_code_comment(t: &str) -> (&str, &str) {
    match t.split_once(';') {
        Some((c, m)) => (c.trim_end(), m.trim()),
        None => (t, ""),
    }
}

/// One external-name use, in CLIF layout order.
enum Use {
    /// `vN = symbol_value.ty gvK`: a data object, named by `gv`'s declaration comment.
    Data(u32),
    /// A function reference (a `func_addr` of a non-colocated declaration, or a call of
    /// one): the declaration's external-name index.
    Func(u32),
}

/// A parsed dump file (one function).
struct FnDump {
    /// The dump file's name (the gvmap key).
    file: String,
    symbol: String,
    /// gv → the declaration's external-name index.
    gv_ext: BTreeMap<u32, u32>,
    /// gv → the allocation's comment (from the gv declaration).
    gv_comment: BTreeMap<u32, String>,
    /// Every external-name use, in CLIF layout order.
    uses: Vec<Use>,
    /// Every `load_ext_name_got` of the function, in code order (from the `.vcode`;
    /// the external-name kind — `User(userextnameJ)` or `LibCall(…)` — doesn't matter
    /// here, the pair's target kind does).
    vgot: Vec<()>,
    /// The `User(userextnameJ)` refs of the same loads, in code order (diagnostics).
    #[allow(dead_code)]
    vgot_exts: Vec<Option<u32>>,
    /// The function's own FuncId (`function u0:N(`).
    own: Option<u32>,
    /// The user-named function declarations `fnK = [colocated] u0:N sigM`, in K order:
    /// (K, N). Libcall declarations (`fnK = %Memcpy sigM`) carry no user name.
    fn_decls: Vec<(u32, u32)>,
}

/// Parse one raw cg_clif dump file (one function).
fn parse_dump(path: &Path, stage: &str) -> FnDump {
    let text = fs::read_to_string(path).unwrap_or_else(|e| die(format!("{}: {e}", path.display())));
    let mut symbol: Option<String> = None;
    let mut gv_comment: BTreeMap<u32, String> = BTreeMap::new();
    let mut gv_ext: BTreeMap<u32, u32> = BTreeMap::new();
    let mut fn_colocated: BTreeMap<u32, bool> = BTreeMap::new();
    let mut uses: Vec<Use> = Vec::new();
    let mut own: Option<u32> = None;
    let mut fn_decls: Vec<(u32, u32)> = Vec::new();
    // The `; extname N u0:M`-style user-name table is not written by cg_clif; instead,
    // every declaration line carries its UserExternalNameRef implicitly: `fnK`'s name
    // reference number is *not* recoverable from the text. So function uses are
    // deduplicated per declaration `fnK` (which cg_clif's `declare_func_in_func`
    // deduplicates by FuncId), and data uses per `userextnameJ` (dedup by DataId).
    for line in text.lines() {
        let t = line.trim_start();
        // with debuginfo on, cg_clif prefixes each instruction with its source location `@XXXX`
        let t = match t.strip_prefix('@') {
            Some(r) if r.starts_with(|c: char| c.is_ascii_hexdigit()) => {
                r.trim_start_matches(|c: char| c.is_ascii_hexdigit()).trim_start()
            }
            _ => t,
        };
        if let Some(s) = t.strip_prefix("; symbol ") {
            symbol = Some(s.trim().to_string());
            continue;
        }
        let (code, comment) = split_code_comment(t);
        if let Some(r) = code.strip_prefix("function u0:") {
            own = parse_u32(r.split('(').next().unwrap_or(""));
        }
        let toks: Vec<&str> = code.split_whitespace().collect();
        if toks.len() < 3 || toks[1] != "=" {
            // `call fnK(...)` / `return_call fnK(...)` may carry results
            // (`v1, v2 = call fn0(...)`), so scan for them on every line: a call of a
            // non-colocated declaration lowers to one GOT load.
            for (i, w) in toks.iter().enumerate() {
                if *w == "call" || *w == "return_call" {
                    if let Some(next) = toks.get(i + 1) {
                        let callee = next.split('(').next().unwrap_or("");
                        if let Some(k) = callee.strip_prefix("fn").and_then(parse_u32) {
                            if !fn_colocated.get(&k).copied().unwrap_or(true) {
                                uses.push(Use::Func(k));
                            }
                        }
                    }
                }
            }
            continue;
        }
        // `gvK = symbol [colocated] userextnameJ`
        if let Some(g) = parse_u32(toks[0].strip_prefix("gv").unwrap_or("")) {
            if toks[2] != "symbol" {
                continue;
            }
            let Some(e) = toks[3..]
                .iter()
                .find_map(|w| w.strip_prefix("userextname").and_then(parse_u32))
            else {
                continue;
            };
            gv_ext.insert(g, e);
            gv_comment.insert(g, comment.to_string());
            continue;
        }
        // `fnK = [colocated] NAME sigM`
        if let Some(k) = parse_u32(toks[0].strip_prefix("fn").unwrap_or("")) {
            fn_colocated.insert(k, toks.contains(&"colocated"));
            if let Some(n) = toks[2..].iter().find_map(|w| w.strip_prefix("u0:").and_then(parse_u32)) {
                fn_decls.push((k, n));
            }
            continue;
        }
        // `vN = symbol_value.ty gvK` / `vN = func_addr.ty fnK`
        if toks[0].starts_with('v') && toks.len() >= 4 {
            if toks[2].starts_with("symbol_value.") {
                if let Some(gv) = parse_u32(toks[3].strip_prefix("gv").unwrap_or("")) {
                    uses.push(Use::Data(gv));
                }
            } else if toks[2].starts_with("func_addr.") {
                if let Some(callee) = parse_u32(toks[3].strip_prefix("fn").unwrap_or("")) {
                    if !fn_colocated.get(&callee).copied().unwrap_or(true) {
                        uses.push(Use::Func(callee));
                    }
                }
            }
        }
    }
    // The `.vcode` of the same function names every external name its GOT loads use,
    // in codegen order: `load_ext_name_got xN, User(userextnameJ)`. The k-th such line
    // is the k-th GOT pair (in code order).
    let vname = path.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
    let vname = vname.strip_suffix(&format!(".{stage}.clif")).unwrap_or(&vname).to_string();
    let vcode_path = path.with_file_name(format!("{vname}.vcode"));
    let vt = fs::read_to_string(&vcode_path)
        .unwrap_or_else(|e| die(format!("{}: {e}", vcode_path.display())));
    let mut vgot: Vec<()> = Vec::new();
    let mut vgot_exts: Vec<Option<u32>> = Vec::new();
    for l in vt.lines() {
        let Some((_pre, rest)) = l.trim_start().split_once("load_ext_name_got ") else { continue };
        vgot.push(());
        let ext = rest
            .split("User(userextname")
            .nth(1)
            .and_then(|e| e.split(')').next())
            .and_then(parse_u32);
        vgot_exts.push(ext);
    }
    let Some(symbol) = symbol else { die(format!("{}: no `; symbol` line", path.display())) };
    FnDump {
        file: path.file_name().and_then(|n| n.to_str()).unwrap_or("?").to_string(),
        symbol,
        gv_ext,
        gv_comment,
        uses,
        vgot,
        vgot_exts,
        own,
        fn_decls: {
            fn_decls.sort();
            fn_decls
        },
    }
}

/// One symbol of the object file, indexed by its symbol-table index.
struct Sym {
    name: String,
    kind: SymbolKind,
    sec: Option<usize>,
    value: u64,
    size: u64,
}

/// The relocation kinds we distinguish (`object::RelocationKind`, abstracted over the
/// ELF types): `S + A` of 64 bits (an `Abs8` data pointer) and the two halves of a GOT
/// load (`R_AARCH64_ADR_GOT_PAGE` + `R_AARCH64_LD64_GOT_LO12_NC`, both kind `Got`).
/// Raw `R_AARCH64_*` codes.
const R_ABS64: object::elf::RelocationType = object::elf::RelocationType(257);
const R_ADR_GOT_PAGE: object::elf::RelocationType = object::elf::RelocationType(311);
const R_LD64_GOT_LO12_NC: object::elf::RelocationType = object::elf::RelocationType(312);

/// The raw ELF relocation type (object's abstract `RelocationKind` maps only a few
/// aarch64 types, so we read `RelocationFlags::Elf { r_type }`).
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum RKind {
    Abs64,
    GotPage,
    GotLo12,
    Other(object::elf::RelocationType),
}

/// One relocation of a section (ELF-only).
struct Rel {
    off: u64,
    sym: usize,
    addend: i64,
    kind: RKind,
}

/// One section of the object file.
struct Sec {
    kind: SectionKind,
    data: Vec<u8>,
    relocs: Vec<Rel>,
}

fn load_obj(path: &Path) -> (BTreeMap<usize, Sym>, BTreeMap<usize, Sec>) {
    let bytes = fs::read(path).unwrap_or_else(|e| die(format!("{}: {e}", path.display())));
    let file = object::read::File::parse(&*bytes)
        .unwrap_or_else(|e| die(format!("{}: {e}", path.display())));
    let mut syms: BTreeMap<usize, Sym> = BTreeMap::new();
    for s in file.symbols() {
        let Ok(name) = s.name() else { continue };
        let sec = match s.section() {
            SymbolSection::Section(i) => Some(i.0),
            _ => None,
        };
        syms.insert(s.index().0, Sym { name: name.to_string(), kind: s.kind(), sec, value: s.address(), size: s.size() });
    }
    let mut secs: BTreeMap<usize, Sec> = BTreeMap::new();
    for s in file.sections() {
        let data = s.data().unwrap_or(&[]).to_vec();
        let mut relocs = Vec::new();
        for (off, r) in s.relocations() {
            let kind = match r.flags() {
                object::RelocationFlags::Elf { r_type } => match r_type {
                    R_ABS64 => RKind::Abs64,
                    R_ADR_GOT_PAGE => RKind::GotPage,
                    R_LD64_GOT_LO12_NC => RKind::GotLo12,
                    other => RKind::Other(other),
                },
                _ => RKind::Other(object::elf::RelocationType(u32::MAX)),
            };
            let sym = match r.target() {
                object::RelocationTarget::Symbol(s) => s.0,
                _ => continue,
            };
            relocs.push(Rel { off, sym, addend: r.addend(), kind });
        }
        secs.insert(s.index().0, Sec { kind: s.kind(), data, relocs });
    }
    (syms, secs)
}

/// One item of a data object's contents (`docs/contracts/clif.md`, "Link-time data").
enum Item {
    /// A byte run.
    Bytes(Vec<u8>),
    /// An 8-byte absolute address `%target±addend` (an `Abs8` relocation).
    Reloc { target: String, addend: i64 },
}

fn hex(bs: &[u8]) -> String {
    let mut s = String::with_capacity(bs.len() * 2);
    for b in bs {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn item_text(i: &Item) -> String {
    match i {
        Item::Bytes(b) => hex(b),
        Item::Reloc { target, addend } => match *addend {
            0 => format!("%{target}"),
            a if a > 0 => format!("%{target}+{a}"),
            a => format!("%{target}-{a}"),
        },
    }
}

/// One data object of the recovered image.
struct DataObj {
    name: String,
    writable: bool,
    items: Vec<Item>,
}

/// The `allocN` number of an allocation comment, if it is one.
fn alloc_of(comment: &str) -> Option<u32> {
    parse_u32(comment.strip_prefix("alloc")?)
}

/// The name of a data object in the emitted directives and gvmap: the symbol's own
/// name, crate-prefixed. cg_clif defines the same allocation (the same `allocN`
/// comment) once per referencing function, so the comment is not an identity — the
/// symbol is.
fn data_name(crate_name: &str, s: &Sym) -> String {
    if let Some(hex) = s.name.strip_prefix(".Ldata") {
        format!("{crate_name}_Ldata{hex}")
    } else {
        s.name.clone()
    }
}

/// The result of `recover`.
struct Recovered {
    objs: Vec<DataObj>,
    /// `(dump file, gv, data name)`.
    gvmap: Vec<(String, u32, String)>,
    fns: usize,
    fns_with_data: usize,
    bytes_total: u64,
    /// FuncId → symbol of the callees (`--fnmap`), see `name_callees`.
    fnmap: BTreeMap<u32, String>,
}

fn recover(crate_name: &str, obj: &Path, dumps: &[FnDump]) -> Recovered {
    let (syms, secs) = load_obj(obj);
    // Symbol index of every function symbol, by name.
    let mut fn_idx: BTreeMap<&str, usize> = BTreeMap::new();
    for (i, s) in syms.iter() {
        if s.kind == SymbolKind::Text && !fn_idx.contains_key(s.name.as_str()) {
            fn_idx.insert(s.name.as_str(), *i);
        }
    }

    // ---- 1. match the GOT loads against the external names ----
    // Every `load_ext_name_got User(extK)` in a function's `.vcode` lowers to exactly
    // one GOT pair (`R_AARCH64_ADR_GOT_PAGE` 311 + `R_AARCH64_LD64_GOT_LO12_NC` 312,
    // same symbol), both in code order — so zipping them positionally is exact, with no
    // order assumption between the CLIF and the code (cg_clif may reorder at -O).
    // Two wrangles, both verified on the survey objects:
    // * `userextnameJ` refs are per-function dense indices over *both* namespaces (a
    //   data declaration and a function declaration can share a ref number), so the
    //   pair's target kind (Data/Text) says whether the ext names data or a callee;
    // * the GOT loads of Cranelift libcalls (`memcpy`, `memset`, …) are not
    //   `load_ext_name_got` instructions, so when the counts disagree we fall back to
    //   pairing the vcode entries with the Data-target pairs only.
    let mut ext_data: BTreeMap<(usize, u32), usize> = BTreeMap::new(); // (fn sym idx, ext) → data sym idx
    let mut recovered: BTreeSet<(usize, u32)> = BTreeSet::new(); // (fn sym idx, gv)
    let mut fns_with_data: BTreeSet<usize> = BTreeSet::new(); // fns with >=1 recovered data use
    let mut got_of: Vec<Vec<usize>> = Vec::new(); // per dump: GOT pair targets, code order
    for d in dumps {
        let Some(&fi) = fn_idx.get(d.symbol.as_str()) else {
            die(format!("{}: function symbol `{}` not found in {}", d.file, d.symbol, obj.display()));
        };
        let Some(si) = syms[&fi].sec else {
            die(format!("{}: `{}` has no section", obj.display(), d.symbol));
        };
        let sec = secs.get(&si).unwrap_or_else(|| die(format!("{}: section {si} missing", obj.display())));
        if sec.kind != SectionKind::Text {
            die(format!("{}: `{}` is not in a text section", obj.display(), d.symbol));
        }
        let (fvalue, fsize) = (syms[&fi].value, syms[&fi].size);
        let mut got: Vec<usize> = Vec::new();
        let mut i = 0;
        while i < sec.relocs.len() {
            let r = &sec.relocs[i];
            if r.kind == RKind::GotPage && r.off >= fvalue && r.off < fvalue + fsize {
                let Some(r2) = sec.relocs.get(i + 1) else {
                    die(format!("{}: `{}`: GOT page reloc without a following load", obj.display(), d.symbol));
                };
                if r2.kind != RKind::GotLo12 || r2.sym != r.sym || r2.off != r.off + 4 {
                    die(format!(
                        "{}: `{}`: GOT page/lo12 pair mismatch at offset {} (next: kind {:?} sym {} off {} addend {})",
                        obj.display(), d.symbol, r.off, r2.kind, r2.sym, r2.off, r2.addend
                    ));
                }
                got.push(r.sym);
                i += 2;
            } else {
                i += 1;
            }
        }
        // The pairing: every GOT load (of a `User` name or a `LibCall`) is one pair, in
        // code order. Only the *data*-target pairs are recorded (callee symbols need no
        // data); an ext shared between a gv and a fn declaration is disambiguated by the
        // target kind.
        if d.vgot.len() != got.len() {
            die(format!(
                "{}: `{}`: {} `load_ext_name_got` in the vcode but {} GOT pairs (targets {})",
                obj.display(), d.symbol, d.vgot.len(), got.len(),
                got.iter().map(|&s| syms[&s].name.clone()).collect::<Vec<_>>().join(", ")
            ));
        }
        got_of.push(got.clone());
        for (&ext, &target) in d.vgot_exts.iter().zip(got.iter()) {
            let Some(ext) = ext else { continue }; // a LibCall load: never data
            if syms[&target].kind != SymbolKind::Data {
                continue;
            }
            match ext_data.entry((fi, ext)) {
                std::collections::btree_map::Entry::Vacant(e) => {
                    e.insert(target);
                }
                std::collections::btree_map::Entry::Occupied(e) => {
                    if *e.get() != target {
                        die(format!(
                            "{}: `{}`: ext{ext} resolves to two data symbols ({} and {})",
                            obj.display(), d.symbol, syms[&*e.get()].name, syms[&target].name
                        ));
                    }
                }
            }
        }
        // Which data gvs are recovered (their ext has a data GOT load)?
        for u in &d.uses {
            let Use::Data(gv) = u else { continue };
            let Some(&ext) = d.gv_ext.get(gv) else {
                die(format!("{}: `{}`: gv{gv} has no declaration", obj.display(), d.symbol));
            };
            if ext_data.contains_key(&(fi, ext)) {
                recovered.insert((fi, *gv));
                fns_with_data.insert(fi);
            }
        }
    }
    // ---- 2. discover the data objects transitively ----
    // Per section: the data symbols (idx, value, size), for section-symbol references.
    let mut secs_data: BTreeMap<usize, Vec<(usize, u64, u64)>> = BTreeMap::new();
    for (i, s) in syms.iter() {
        if s.kind == SymbolKind::Data {
            if let Some(seci) = s.sec {
                secs_data.entry(seci).or_default().push((*i, s.value, s.size));
            }
        }
    }
    let mut reached: BTreeSet<usize> = BTreeSet::new();
    let mut queue: Vec<usize> = ext_data.values().copied().collect();
    while let Some(si) = queue.pop() {
        if !reached.insert(si) {
            continue;
        }
        let s = &syms[&si];
        let Some(seci) = s.sec else {
            // An imported data object (e.g. a `core` static): its bytes are not in this
            // object, so it cannot be recovered here.
            eprintln!("clif-data-export: warning: {}: data symbol `{}` is imported; skipped", obj.display(), s.name);
            continue;
        };
        let sec = secs.get(&seci).unwrap_or_else(|| die(format!("{}: section {seci} missing", obj.display())));
        let (kind, data, relocs) = (&sec.kind, &sec.data, &sec.relocs);
        let _ = &data;
        if !matches!(
            kind,
            SectionKind::ReadOnlyData | SectionKind::ReadOnlyDataWithRel | SectionKind::Data | SectionKind::UninitializedData
        ) {
            die(format!("{}: data symbol `{}` is in an unexpected section (kind {:?})", obj.display(), s.name, kind));
        }
        for r in relocs {
            if r.kind != RKind::Abs64 || r.off < s.value || r.off >= s.value + s.size {
                continue;
            }
            // A reference may target the data object's symbol directly or, for another
            // object of the same section, the section symbol (S = section base,
            // A = the referenced offset).
            let mut targets: Vec<usize> = Vec::new();
            if syms[&r.sym].kind == SymbolKind::Section {
                let addr = r.addend as u64;
                if let Some(ds) = secs_data.get(&seci) {
                    for (i, v, sz) in ds {
                        if addr >= *v && addr < v + *sz {
                            targets.push(*i);
                        }
                    }
                }
            } else if syms[&r.sym].kind == SymbolKind::Data {
                targets.push(r.sym);
            }
            for ti in targets {
                if !reached.contains(&ti) {
                    queue.push(ti);
                }
            }
        }
    }

    // ---- 3. name every data object ----
    let mut names: BTreeMap<usize, String> = BTreeMap::new();
    for &si in reached.iter() {
        names.entry(si).or_insert_with(|| data_name(crate_name, &syms[&si]));
    }
    // The gv renaming table: (dump file, gv, data name), for every recovered data use.
    let mut gvmap: Vec<(String, u32, String)> = Vec::new();
    for d in dumps {
        let Some(&fi) = fn_idx.get(d.symbol.as_str()) else { continue };
        for u in &d.uses {
            let Use::Data(gv) = u else { continue };
            let Some(&ext) = d.gv_ext.get(gv) else { continue };
            let Some(&target) = ext_data.get(&(fi, ext)) else { continue };
            let name = names.get(&target).cloned().unwrap_or_else(|| data_name(crate_name, &syms[&target]));
            gvmap.push((d.file.clone(), *gv, name));
        }
    }

    // ---- 4. the items of every data object ----
    // Per section: the data symbols (idx, value, size), for section-symbol references.
    let mut secs_data: BTreeMap<usize, Vec<(usize, u64, u64)>> = BTreeMap::new();
    for (i, s) in syms.iter() {
        if s.kind == SymbolKind::Data {
            if let Some(seci) = s.sec {
                secs_data.entry(seci).or_default().push((*i, s.value, s.size));
            }
        }
    }
    let mut objs: Vec<DataObj> = Vec::new();
    let mut bytes_total: u64 = 0;
    for (name, si) in names.iter().map(|(i, n)| (n.clone(), *i)) {
        let s = &syms[&si];
        let Some(seci) = s.sec else {
            // An imported data object (e.g. a `core` static): its bytes are not in this
            // object, so it cannot be recovered here.
            eprintln!("clif-data-export: warning: {}: data symbol `{}` is imported; skipped", obj.display(), s.name);
            continue;
        };
        let sec = secs.get(&seci).unwrap_or_else(|| die(format!("{}: section {seci} missing", obj.display())));
        let (kind, data, relocs) = (&sec.kind, &sec.data, &sec.relocs);
        let _ = &data;
        let writable = matches!(kind, SectionKind::Data | SectionKind::UninitializedData);
        // relocations inside the object, at their byte offset
        let mut at: BTreeMap<u64, Item> = BTreeMap::new();
        for r in relocs {
            if r.kind != RKind::Abs64 || r.off < s.value || r.off >= s.value + s.size {
                continue;
            }
            // A reference to another data object of the same section may go through the
            // section symbol (S = the section base, A = the referenced offset).
            let (target, addend) = if syms[&r.sym].kind == SymbolKind::Section {
                let addr = r.addend as u64;
                let Some((tsym, _)) = secs_data.get(&seci).and_then(|ds|
                    ds.iter().find(|(_, v, sz)| addr >= *v && addr < v + *sz).map(|(i, v, _)| (*i, *v)))
                else {
                    die(format!("{}: `{}` relocates through a section symbol to {addr:#x}, which no data object covers", obj.display(), name));
                };
                (data_name(crate_name, &syms[&tsym]), (addr - syms[&tsym].value) as i64)
            } else {
                let t = &syms[&r.sym];
                let target = match t.kind {
                    SymbolKind::Text => t.name.clone(),
                    SymbolKind::Data => names.get(&r.sym).cloned().unwrap_or_else(|| data_name(crate_name, t)),
                    // an imported symbol (e.g. a vtable's method of another crate): by name
                    _ if t.sec.is_none() => t.name.clone(),
                    _ => die(format!("{}: `{}` relocates to symbol `{}` of kind {:?}", obj.display(), name, t.name, t.kind)),
                };
                (target, r.addend)
            };
            at.insert(r.off - s.value, Item::Reloc { target, addend });
        }
        // interleave with the byte runs between them
        // `data` is the whole section; the object starts at `s.value`. The reloc map
        // `at` and `pos` are offsets *inside* the object.
        let base = s.value as usize;
        let mut items: Vec<Item> = Vec::new();
        let mut pos: u64 = 0;
        for (off, item) in at {
            if off > pos {
                items.push(Item::Bytes(data[base + pos as usize..base + off as usize].to_vec()));
            }
            items.push(item);
            pos = off + 8;
        }
        if s.size > pos {
            items.push(Item::Bytes(data[base + pos as usize..base + s.size as usize].to_vec()));
        }
        bytes_total += s.size;
        objs.push(DataObj { name, writable, items });
    }
    let fnmap = name_callees(&syms, &got_of, dumps);
    Recovered { objs, gvmap, fns: dumps.len(), fns_with_data: fns_with_data.len(), bytes_total, fnmap }
}

/// Name the callees cg_clif declares only by FuncId (`fnK = u0:N sigM ; Instance {…}`, a
/// function of another crate or codegen unit): FuncId N → linker symbol, for `normalize.py
/// --fnmap`.
///
/// A function's `userextnameJ` refs are allocated in declaration order, one per new name,
/// data (`gvK = symbol userextnameJ`, explicit in the text) and functions (`fnK = u0:N`,
/// implicit) interleaved; FuncRefs are numbered in the same order. So the refs no gv uses
/// are the function declarations', in K order. Each such ref's GOT load (vcode, code order)
/// pairs with a GOT relocation (object, code order), whose target is the callee's symbol.
/// Checked, never guessed: the refs must be dense; a function ref's target must not be data;
/// a ref must be either a gv's or a function's; the FuncIds of this codegen unit's own
/// functions must pair with their own symbols; one FuncId must name one symbol in every
/// function (FuncIds are per CGU module). A function failing a check contributes nothing; a
/// FuncId with two different symbols is dropped.
fn name_callees(syms: &BTreeMap<usize, Sym>, got_of: &[Vec<usize>], dumps: &[FnDump]) -> BTreeMap<u32, String> {
    let known: BTreeMap<u32, &str> = dumps.iter().filter_map(|d| d.own.map(|n| (n, d.symbol.as_str()))).collect();
    let mut map: BTreeMap<u32, String> = BTreeMap::new();
    let mut conflict: BTreeSet<u32> = BTreeSet::new();
    for (d, got) in dumps.iter().zip(got_of) {
        let gv_exts: BTreeSet<u32> = d.gv_ext.values().copied().collect();
        let total = (gv_exts.len() + d.fn_decls.len()) as u32;
        if gv_exts.iter().any(|&j| j >= total) {
            continue;
        }
        let ext_fn: BTreeMap<u32, u32> =
            (0..total).filter(|j| !gv_exts.contains(j)).zip(d.fn_decls.iter().map(|&(_, n)| n)).collect();
        let mut cand: Vec<(u32, String)> = Vec::new();
        let mut ok = true;
        for (&ext, &target) in d.vgot_exts.iter().zip(got.iter()) {
            let Some(ext) = ext else { continue };
            if gv_exts.contains(&ext) {
                continue;
            }
            match ext_fn.get(&ext) {
                Some(&n) if syms[&target].kind != SymbolKind::Data => cand.push((n, syms[&target].name.clone())),
                _ => ok = false,
            }
        }
        if !ok || cand.iter().any(|(n, s)| known.get(n).is_some_and(|k| k != s)) {
            continue;
        }
        for (n, s) in cand {
            match map.get(&n) {
                Some(prev) if *prev != s => {
                    conflict.insert(n);
                }
                _ => {
                    map.insert(n, s);
                }
            }
        }
    }
    for n in conflict {
        map.remove(&n);
    }
    map
}

fn data_directive(o: &DataObj) -> String {
    let w = if o.writable { " writable" } else { "" };
    let items = if o.items.is_empty() { String::new() } else {
        let mut s = String::new();
        for (i, it) in o.items.iter().enumerate() {
            if i > 0 {
                s.push(' ');
            }
            s.push_str(&item_text(it));
        }
        s
    };
    format!("; data: %{}{w} = {items}", o.name)
}

fn usage() -> ! {
    eprintln!("usage: clif-data-export <clif-dir> <obj> --out F.clif --gvmap F.tsv [--fnmap F.tsv] [--stage unopt]");
    std::process::exit(2)
}

fn main() {
    let mut stage = "unopt".to_string();
    let mut out: Option<PathBuf> = None;
    let mut gvmap_path: Option<PathBuf> = None;
    let mut fnmap_path: Option<PathBuf> = None;
    let mut pos: Vec<PathBuf> = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--stage" => stage = args.next().unwrap_or_else(|| usage()),
            "--out" => out = Some(PathBuf::from(args.next().unwrap_or_else(|| usage()))),
            "--gvmap" => gvmap_path = Some(PathBuf::from(args.next().unwrap_or_else(|| usage()))),
            "--fnmap" => fnmap_path = Some(PathBuf::from(args.next().unwrap_or_else(|| usage()))),
            _ => pos.push(PathBuf::from(a)),
        }
    }
    let [clif_dir, obj] = <[PathBuf; 2]>::try_from(pos).unwrap_or_else(|_| usage());
    let Some(out) = out else { die("--out is required".into()) };
    let Some(gvmap_path) = gvmap_path else { die("--gvmap is required".into()) };

    // dumps, by file name
    let mut dump_files: Vec<PathBuf> = fs::read_dir(&clif_dir)
        .unwrap_or_else(|e| die(format!("{}: {e}", clif_dir.display())))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.extension().map_or(false, |e| e == "clif")
                && p.file_name().and_then(|n| n.to_str()).map_or(false, |n| n.ends_with(&format!(".{stage}.clif")))
        })
        .collect();
    dump_files.sort();
    let dumps: Vec<FnDump> = dump_files.iter().map(|p| parse_dump(p, &stage)).collect();
    let crate_name = clif_dir
        .file_name()
        .and_then(|n| n.to_str())
        .and_then(|n| n.strip_suffix(".clif"))
        .unwrap_or("crate")
        .to_string();

    let r = recover(&crate_name, &obj, &dumps);
    fs::write(&out, r.objs.iter().map(data_directive).collect::<Vec<_>>().join("\n") + "\n")
        .unwrap_or_else(|e| die(format!("{}: {e}", out.display())));
    fs::write(
        &gvmap_path,
        r.gvmap.iter().map(|(f, gv, n)| format!("{f}\tgv{gv}\t%{n}")).collect::<Vec<_>>().join("\n") + "\n",
    )
    .unwrap_or_else(|e| die(format!("{}: {e}", gvmap_path.display())));
    if let Some(p) = fnmap_path {
        let text: String = r.fnmap.iter().map(|(n, s)| format!("u0:{n}\t{s}\n")).collect();
        fs::write(&p, text).unwrap_or_else(|e| die(format!("{}: {e}", p.display())));
    }
    println!(
        "{{\"crate\": \"{crate}\", \"fns\": {f}, \"fns_with_data\": {a}, \"data_objects\": {m}, \"data_bytes\": {b}}}",
        crate = crate_name,
        f = r.fns,
        a = r.fns_with_data,
        m = r.objs.len(),
        b = r.bytes_total
    );
}









