//! Cranelift compilation with the project's verification-friendly settings (PLAN.md §4 M1,
//! Appendix A), shared by the `clif2obj` driver and `clif-native`.
//!
//! * [`isa`] builds the target ISA with exactly `opt_level=none`, `enable_verifier=true`,
//!   `regalloc_checker=true`, `is_pic=true` (every other setting at its default).
//! * [`ObjectCompiler`] compiles parsed CLIF functions into one relocatable object. Every
//!   function named `%name` becomes the exported symbol `name`; a `fnN = %callee(...)`
//!   declaration that is not one of the object's functions becomes an undefined (imported)
//!   symbol `callee`. For each function it returns a [`CompiledFunc`] with the machine code,
//!   the VCode disassembly, the relocations and the trap table ([`CompiledFunc::write_dump`]
//!   writes them; schemas in `docs/contracts/drivers.md`).

use std::collections::HashMap;
use std::path::Path;
use std::str::FromStr;

use anyhow::{Context as _, Result, anyhow, bail};
use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::ir::{ExternalName, Function, GlobalValueData, UserExternalName, UserFuncName};
use cranelift_codegen::isa::{self, OwnedTargetIsa};
use cranelift_codegen::FinalizedRelocTarget;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::{CodegenError, Context};
use cranelift_module::{DataId, FuncId, Linkage, Module, ModuleError};
use cranelift_object::{ObjectBuilder, ObjectModule};
use cranelift_reader::{ParseOptions, TestFile};
use serde_json::{Value, json};

/// The fixed code generator settings (name, value), applied on top of Cranelift's defaults.
pub const SETTINGS: [(&str, &str); 4] = [
    ("opt_level", "none"),
    ("enable_verifier", "true"),
    ("regalloc_checker", "true"),
    ("is_pic", "true"),
];

/// Target ISA for `triple` (e.g. `aarch64-unknown-linux-gnu`) with [`SETTINGS`].
pub fn isa(triple: &str) -> Result<OwnedTargetIsa> {
    isa_with_opt_level(triple, "none")
}

/// [`isa`] with `opt_level` overridden (`none`, `speed`, `speed_and_size`). Only for
/// measuring Cranelift's optimiser (`scripts/lean-backend-metrics.sh`); every checked path
/// uses [`isa`].
pub fn isa_with_opt_level(triple: &str, opt_level: &str) -> Result<OwnedTargetIsa> {
    let mut flags = settings::builder();
    for (name, value) in SETTINGS {
        let value = if name == "opt_level" { opt_level } else { value };
        flags.set(name, value).with_context(|| format!("setting {name}={value}"))?;
    }
    let triple = target_lexicon::Triple::from_str(triple).map_err(|e| anyhow!("triple {triple}: {e}"))?;
    let builder = isa::lookup(triple.clone()).with_context(|| format!("no ISA for {triple}"))?;
    builder
        .finish(settings::Flags::new(flags))
        .with_context(|| format!("building the ISA for {triple}"))
}

/// Parses a .clif file. `test`/`target`/`set` header lines are accepted but do not affect
/// code generation (the ISA and settings come from [`isa`]). Signatures without an explicit
/// calling convention get the target's C calling convention (`system_v` for
/// `aarch64-unknown-linux-gnu`, PLAN.md §3.2) instead of the reader's default `fast`; a
/// file with a `test run` line gets the host's C calling convention (cranelift-reader rule),
/// which is also `system_v` on x86-64 Linux hosts.
pub fn parse_file<'a>(text: &'a str, isa: &dyn isa::TargetIsa) -> Result<TestFile<'a>> {
    let opts = ParseOptions { default_calling_convention: isa.default_call_conv(), ..ParseOptions::default() };
    cranelift_reader::parse_test(text, opts).map_err(|e| anyhow!("{e}"))
}

/// Options that change how externs are referenced.
#[derive(Clone, Copy, Debug, Default)]
pub struct Options {
    /// Treat every `fnN` declaration as `colocated` (direct `bl` with an `Arm64Call`
    /// relocation instead of a GOT load), as if written `fnN = colocated %callee(...)`.
    pub colocated_externs: bool,
}

/// Symbol name of a CLIF test-case name `%foo` (`foo`).
pub fn symbol_name(name: &UserFuncName) -> Result<String> {
    match name {
        UserFuncName::Testcase(t) => Ok(t.to_string().trim_start_matches('%').to_string()),
        UserFuncName::User(u) => bail!("expected a %name function name, got {u}"),
    }
}

fn ext_symbol_name(name: &ExternalName) -> Result<String> {
    match name {
        ExternalName::TestCase(t) => Ok(t.to_string().trim_start_matches('%').to_string()),
        other => bail!("expected a %name callee, got {other:?}"),
    }
}

/// Symbols of the functions `func` references through `fnN` declarations.
pub fn callees(func: &Function) -> Result<Vec<String>> {
    func.dfg.ext_funcs.values().map(|ext| ext_symbol_name(&ext.name)).collect()
}

/// One relocation of a compiled function (`<name>.relocs.json` entry).
#[derive(Clone, Debug)]
pub struct RelocRecord {
    /// Byte offset of the relocated instruction from the start of the function.
    pub offset: u32,
    /// Cranelift's `Reloc` variant name, e.g. `Aarch64AdrGotPage21`, `Arm64Call`.
    pub kind: String,
    /// Target symbol. A reference to an offset inside the function itself is expressed
    /// against the function's own symbol with the offset added to `addend` (as
    /// `cranelift-object` emits it).
    pub target: String,
    pub addend: i64,
}

/// One trap site (`<name>.traps.json` entry).
#[derive(Clone, Debug)]
pub struct TrapRecord {
    /// Byte offset of the trapping instruction (`udf`, or a load/store that may fault).
    pub offset: u32,
    /// Trap code name as printed in CLIF (`int_ovf`, `heap_oob`, `user7`, ...).
    pub code: String,
}

/// The compilation result of one function.
#[derive(Clone, Debug)]
pub struct CompiledFunc {
    /// Symbol name (the CLIF name without `%`).
    pub name: String,
    /// The function as Cranelift parsed it (before lowering and before extern renaming).
    pub clif: String,
    /// Machine code (the function's bytes in the text section, including constant islands).
    pub code: Vec<u8>,
    /// VCode disassembly (post-regalloc machine instructions) from `Context::set_disasm`.
    pub vcode: Option<String>,
    pub relocs: Vec<RelocRecord>,
    pub traps: Vec<TrapRecord>,
}

impl CompiledFunc {
    pub fn relocs_json(&self) -> Value {
        Value::Array(
            self.relocs
                .iter()
                .map(|r| json!({"offset": r.offset, "kind": r.kind, "target": r.target, "addend": r.addend}))
                .collect(),
        )
    }

    pub fn traps_json(&self) -> Value {
        Value::Array(
            self.traps
                .iter()
                .map(|t| json!({"offset": t.offset, "code": t.code}))
                .collect(),
        )
    }

    /// Writes `<name>.bin`, `<name>.clif`, `<name>.vcode` (if available),
    /// `<name>.relocs.json` and `<name>.traps.json` into `dir`.
    pub fn write_dump(&self, dir: &Path) -> Result<()> {
        let base = dir.join(&self.name);
        let path = |ext: &str| base.with_extension(ext);
        std::fs::write(path("bin"), &self.code)?;
        std::fs::write(path("clif"), &self.clif)?;
        if let Some(v) = &self.vcode {
            std::fs::write(path("vcode"), v)?;
        }
        std::fs::write(path("relocs.json"), format!("{:#}\n", self.relocs_json()))?;
        std::fs::write(path("traps.json"), format!("{:#}\n", self.traps_json()))?;
        Ok(())
    }
}

fn codegen_error(func: &Function, e: CodegenError) -> anyhow::Error {
    match e {
        CodegenError::Verifier(errors) => anyhow!(
            "verifier errors:\n{}",
            cranelift_codegen::print_errors::pretty_verifier_error(func, None, errors)
        ),
        other => anyhow!("{other}"),
    }
}

/// Compiles `func` on its own (no object, extern names untouched): used to find out which
/// functions of a file Cranelift accepts before building an object from them.
pub fn check_compiles(isa: &dyn isa::TargetIsa, func: &Function) -> Result<()> {
    let mut ctx = Context::for_function(func.clone());
    ctx.compile(isa, &mut ControlPlane::default())
        .map(|_| ())
        .map_err(|e| codegen_error(&e.func.clone(), e.inner))
}

/// Builds one relocatable object from CLIF functions.
pub struct ObjectCompiler {
    module: ObjectModule,
    ids: HashMap<String, FuncId>,
    data_ids: HashMap<String, DataId>,
    opts: Options,
    ctx: Context,
}

impl ObjectCompiler {
    pub fn new(isa: OwnedTargetIsa, opts: Options) -> Result<Self> {
        let builder = ObjectBuilder::new(isa, "clif", cranelift_module::default_libcall_names())?;
        Ok(Self { module: ObjectModule::new(builder), ids: HashMap::new(), data_ids: HashMap::new(), opts, ctx: Context::new() })
    }

    /// Declares `funcs` as exported functions of the object. Every function must be
    /// declared before any function that calls it is defined, so that the call resolves
    /// to it rather than to an import.
    pub fn declare(&mut self, funcs: &[&Function]) -> Result<()> {
        for f in funcs {
            let name = symbol_name(&f.name)?;
            if self.ids.contains_key(&name) {
                bail!("function %{name} is defined twice");
            }
            let id = self
                .module
                .declare_function(&name, Linkage::Export, &f.signature)
                .map_err(|e| anyhow!("declaring %{name}: {e}"))?;
            self.ids.insert(name, id);
        }
        Ok(())
    }

    /// Compiles and defines a declared function.
    pub fn define(&mut self, func: &Function) -> Result<CompiledFunc> {
        let name = symbol_name(&func.name)?;
        let id = *self.ids.get(&name).ok_or_else(|| anyhow!("%{name} was not declared"))?;
        let clif = func.display().to_string();
        let mut f = func.clone();

        // `gvN = symbol [colocated] %sym` → imported data symbol `sym` (defined by a linked
        // object, e.g. `clif-native`'s `; data:` objects).
        let gvs: Vec<_> = f.global_values.keys().collect();
        for gv in gvs {
            let GlobalValueData::Symbol { name: sym, .. } = &f.global_values[gv] else { continue };
            let ExternalName::TestCase(t) = sym else {
                bail!("%{name}: unsupported symbol global value {sym:?}")
            };
            let dname = t.to_string().trim_start_matches('%').to_string();
            let did = match self.data_ids.get(&dname) {
                Some(id) => *id,
                None => {
                    let id = self
                        .module
                        .declare_data(&dname, Linkage::Import, false, false)
                        .map_err(|e| anyhow!("%{name}: declaring data %{dname}: {e}"))?;
                    self.data_ids.insert(dname, id);
                    id
                }
            };
            let r = f.params.ensure_user_func_name(UserExternalName::new(1, did.as_u32()));
            if let GlobalValueData::Symbol { name, .. } = &mut f.global_values[gv] {
                *name = ExternalName::user(r);
            }
        }

        // `fnN = %callee(...)` → module symbol `callee` (an import unless declared).
        let refs: Vec<_> = f.dfg.ext_funcs.keys().collect();
        for fr in refs {
            let callee = ext_symbol_name(&f.dfg.ext_funcs[fr].name)?;
            let sig = f.dfg.signatures[f.dfg.ext_funcs[fr].signature].clone();
            let cid = match self.ids.get(&callee) {
                Some(id) => *id,
                None => {
                    let id = self
                        .module
                        .declare_function(&callee, Linkage::Import, &sig)
                        .map_err(|e| anyhow!("%{name}: declaring extern %{callee}: {e}"))?;
                    self.ids.insert(callee, id);
                    id
                }
            };
            let r = f.params.ensure_user_func_name(UserExternalName::new(0, cid.as_u32()));
            let ext = &mut f.dfg.ext_funcs[fr];
            ext.name = ExternalName::user(r);
            if self.opts.colocated_externs {
                ext.colocated = true;
            }
        }

        self.ctx.clear();
        self.ctx.func = f;
        self.ctx.set_disasm(true);
        if let Err(e) = self.module.define_function(id, &mut self.ctx) {
            return Err(match e {
                ModuleError::Compilation(ce) => codegen_error(&self.ctx.func, ce),
                other => anyhow!("{other}"),
            })
            .with_context(|| format!("compiling %{name}"));
        }
        let code = self.ctx.compiled_code().ok_or_else(|| anyhow!("no code for %{name}"))?;
        let buffer = &code.buffer;
        let mut relocs = Vec::new();
        for r in buffer.relocs() {
            let (target, addend) = match &r.target {
                FinalizedRelocTarget::ExternalName(ExternalName::User(u)) => {
                    let uname = &self.ctx.func.params.user_named_funcs()[*u];
                    if uname.namespace == 1 {
                        let did = DataId::from_u32(uname.index);
                        (self.module.declarations().get_data_decl(did).linkage_name(did).into_owned(), r.addend)
                    } else {
                        let fid = FuncId::from_u32(uname.index);
                        (self.module.declarations().get_function_decl(fid).linkage_name(fid).into_owned(), r.addend)
                    }
                }
                FinalizedRelocTarget::ExternalName(ExternalName::LibCall(lc)) => {
                    ((cranelift_module::default_libcall_names())(*lc), r.addend)
                }
                FinalizedRelocTarget::ExternalName(ExternalName::KnownSymbol(ks)) => (format!("{ks:?}"), r.addend),
                FinalizedRelocTarget::ExternalName(ExternalName::TestCase(t)) => {
                    bail!("%{name}: unexpected test-case relocation target {t}")
                }
                FinalizedRelocTarget::Func(off) => (name.clone(), r.addend + i64::from(*off)),
            };
            relocs.push(RelocRecord { offset: r.offset, kind: format!("{:?}", r.kind), target, addend });
        }
        let traps = buffer
            .traps()
            .iter()
            .map(|t| TrapRecord { offset: t.offset, code: t.code.to_string() })
            .collect();
        Ok(CompiledFunc {
            name,
            clif,
            code: code.code_buffer().to_vec(),
            vcode: code.vcode.clone(),
            relocs,
            traps,
        })
    }

    /// The object file bytes.
    pub fn finish(self) -> Result<Vec<u8>> {
        self.module.finish().emit().map_err(|e| anyhow!("emitting the object: {e}"))
    }
}
