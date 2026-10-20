//! The data objects of a cg_clif object file, as `; data:` directives
//! (`docs/contracts/clif.md`, "Link-time data"; `docs/contracts/frontend.md`).
//!
//! usage: clif-data-export <obj> --out F.clif
//!
//! cg_clif puts the bytes of every data object (panic `Location`s and messages, constant
//! tables, constant enum values, vtables, statics) only into its object file. This tool writes
//! one `; data:` directive per data symbol defined in the object: its bytes and its 64-bit
//! absolute relocations as `%target±addend`. It reads the object only: which data object a
//! function's global value denotes is in cg_clif's dump (its external-name table, the patched
//! cg_clif of `scripts/build-cg-clif.sh`), and the data a program reaches is computed in Lean
//! (`Front.parseUnit`, `reachSet`).
//!
//! Names: an anonymous object `.Ldata<hex>` is `c_Ldata<hex>` (its CLIF name, `Front.clifName`),
//! every other symbol its own name. A relocation through a section symbol is resolved to the
//! data object of that section covering the target offset.
//!
//! An object that cannot be described exactly — a relocation other than `R_AARCH64_ABS64`, one
//! that overlaps another or the object's end, a section-relative target no data object covers, a
//! symbol in a section that is not data — gets a directive that does not parse
//! (`; data: %name unsupported: …`): `Front.parseUnit` rejects a unit whose functions reach it.
use object::read::{Object, ObjectSection, ObjectSymbol, SymbolSection};
use object::{SectionKind, SymbolKind};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

fn die(msg: String) -> ! {
    eprintln!("clif-data-export: {msg}");
    std::process::exit(1)
}

/// One symbol of the object file, indexed by its symbol-table index.
struct Sym {
    name: String,
    kind: SymbolKind,
    sec: Option<usize>,
    value: u64,
    size: u64,
}

/// `R_AARCH64_ABS64`: `S + A`, 64 bits (an `Abs8` data pointer).
const R_ABS64: u32 = 257;

/// One relocation of a section (ELF-only): offset, target symbol, addend, raw ELF type.
struct Rel {
    off: u64,
    sym: usize,
    addend: i64,
    r_type: u32,
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
        let data = if s.kind() == SectionKind::UninitializedData {
            Vec::new()
        } else {
            s.data().unwrap_or_else(|e| die(format!("{}: section {}: {e}", path.display(), s.index().0))).to_vec()
        };
        let mut relocs = Vec::new();
        for (off, r) in s.relocations() {
            let r_type = match r.flags() {
                object::RelocationFlags::Elf { r_type } => r_type.0,
                _ => u32::MAX,
            };
            let sym = match r.target() {
                object::RelocationTarget::Symbol(s) => s.0,
                _ => usize::MAX,
            };
            relocs.push(Rel { off, sym, addend: r.addend(), r_type });
        }
        secs.insert(s.index().0, Sec { kind: s.kind(), data, relocs });
    }
    (syms, secs)
}

/// The CLIF name of an object symbol (`Front.clifName`).
fn clif_name(s: &str) -> String {
    match s.strip_prefix(".Ldata") {
        Some(hex) => format!("c_Ldata{hex}"),
        None => s.to_string(),
    }
}

fn hex(bs: &[u8]) -> String {
    let mut s = String::with_capacity(bs.len() * 2);
    for b in bs {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// A relocation target: `%target`, `%target+a`, `%target-a`.
fn reloc_text(target: &str, addend: i64) -> String {
    match addend {
        0 => format!("%{target}"),
        a if a > 0 => format!("%{target}+{a}"),
        a => format!("%{target}{a}"),
    }
}

/// The `; data:` directive of the data symbol `s`, or why it cannot be described.
fn directive(syms: &BTreeMap<usize, Sym>, secs: &BTreeMap<usize, Sec>, s: &Sym, seci: usize) -> Result<String, String> {
    let sec = secs.get(&seci).ok_or_else(|| format!("section {seci} missing"))?;
    let writable = match sec.kind {
        SectionKind::ReadOnlyData | SectionKind::ReadOnlyDataWithRel | SectionKind::ReadOnlyString => false,
        SectionKind::Data | SectionKind::UninitializedData => true,
        k => return Err(format!("in a section of kind {k:?}")),
    };
    let bss = sec.kind == SectionKind::UninitializedData;
    if !bss && s.value + s.size > sec.data.len() as u64 {
        return Err("extends past its section".into());
    }
    // the relocations inside the object, at their offset in it
    let mut at: BTreeMap<u64, String> = BTreeMap::new();
    for r in &sec.relocs {
        if r.off + 8 <= s.value || r.off >= s.value + s.size {
            continue;
        }
        if r.r_type != R_ABS64 {
            return Err(format!("relocation of type {} at +{}", r.r_type, r.off as i64 - s.value as i64));
        }
        if r.off < s.value || r.off + 8 > s.value + s.size {
            return Err(format!("relocation across the object's bounds at +{}", r.off as i64 - s.value as i64));
        }
        let t = syms.get(&r.sym).ok_or_else(|| format!("relocation to symbol {} (none)", r.sym))?;
        let text = if t.kind == SymbolKind::Section {
            // a section-relative reference: the data object of that section covering the offset
            let addr = r.addend as u64;
            let Some(o) = syms.values().find(|o| {
                o.kind == SymbolKind::Data && o.sec == t.sec && addr >= o.value && addr < o.value + o.size
            }) else {
                return Err(format!("relocation through a section symbol to {addr:#x}, which no data object covers"));
            };
            reloc_text(&clif_name(&o.name), (addr - o.value) as i64)
        } else {
            reloc_text(&clif_name(&t.name), r.addend)
        };
        at.insert(r.off - s.value, text);
    }
    let mut items: Vec<String> = Vec::new();
    let mut pos: u64 = 0;
    let bytes = |a: u64, b: u64| -> String {
        if bss { "00".repeat((b - a) as usize) } else { hex(&sec.data[(s.value + a) as usize..(s.value + b) as usize]) }
    };
    for (off, text) in at {
        if off < pos {
            return Err(format!("overlapping relocations at +{off}"));
        }
        if off > pos {
            items.push(bytes(pos, off));
        }
        items.push(text);
        pos = off + 8;
    }
    if s.size > pos {
        items.push(bytes(pos, s.size));
    }
    let w = if writable { " writable" } else { "" };
    Ok(format!("; data: %{}{w} = {}", clif_name(&s.name), items.join(" ")))
}

fn usage() -> ! {
    eprintln!("usage: clif-data-export <obj> --out F.clif");
    std::process::exit(2)
}

fn main() {
    let mut out: Option<PathBuf> = None;
    let mut pos: Vec<PathBuf> = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--out" => out = Some(PathBuf::from(args.next().unwrap_or_else(|| usage()))),
            _ if a.starts_with("--") => usage(),
            _ => pos.push(PathBuf::from(a)),
        }
    }
    let [obj] = <[PathBuf; 1]>::try_from(pos).unwrap_or_else(|_| usage());
    let Some(out) = out else { usage() };
    let (syms, secs) = load_obj(&obj);
    let mut lines: Vec<String> = Vec::new();
    let (mut objects, mut bytes, mut unsupported) = (0usize, 0u64, 0usize);
    for s in syms.values() {
        let (SymbolKind::Data, Some(seci)) = (s.kind, s.sec) else { continue };
        match directive(&syms, &secs, s, seci) {
            Ok(l) => {
                objects += 1;
                bytes += s.size;
                lines.push(l);
            }
            Err(why) => {
                unsupported += 1;
                lines.push(format!("; data: %{} unsupported: {why}", clif_name(&s.name)));
            }
        }
    }
    fs::write(&out, lines.join("\n") + "\n").unwrap_or_else(|e| die(format!("{}: {e}", out.display())));
    println!(
        "{{\"object\": \"{}\", \"data_objects\": {objects}, \"data_bytes\": {bytes}, \"unsupported\": {unsupported}}}",
        obj.display()
    );
}
