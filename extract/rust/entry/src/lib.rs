//! Extraction root: the stock Cranelift AArch64 compile path, CLIF text to code artifacts.
//!
//! Charon/Aeneas start here (`compile_aarch64`, `triple`). Everything below is the unchanged
//! pinned Cranelift; this crate only wires the stock calls together in stock order
//! (`cranelift_reader::parse_functions`, flag builders, `AArch64Backend::new_with_flags`,
//! `Context::compile`) and computes alignment exactly as the filetests' `write_code`.
use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::ir::Function;
use cranelift_codegen::isa::TargetIsa;
use cranelift_codegen::isa::aarch64::{self, AArch64Backend};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::{CodegenError, Context, FinalizedMachReloc, MachTrap};
use target_lexicon::{
    Aarch64Architecture, Architecture, BinaryFormat, Environment, OperatingSystem, Triple, Vendor,
};

/// Every target triple the pinned AArch64 filetests compile for.
pub enum TargetSpec {
    Aarch64UnknownUnknown,
    Aarch64UnknownUnknownElf,
    Aarch64UnknownLinuxGnu,
    Aarch64AppleDarwin,
}

/// The triple for `spec`, built as a struct literal (no string parsing).
pub fn triple(spec: TargetSpec) -> Triple {
    let (vendor, operating_system, environment, binary_format) = match spec {
        TargetSpec::Aarch64UnknownUnknown => (
            Vendor::Unknown,
            OperatingSystem::Unknown,
            Environment::Unknown,
            BinaryFormat::Unknown,
        ),
        TargetSpec::Aarch64UnknownUnknownElf => (
            Vendor::Unknown,
            OperatingSystem::Unknown,
            Environment::Unknown,
            BinaryFormat::Elf,
        ),
        TargetSpec::Aarch64UnknownLinuxGnu => (
            Vendor::Unknown,
            OperatingSystem::Linux,
            Environment::Gnu,
            BinaryFormat::Elf,
        ),
        TargetSpec::Aarch64AppleDarwin => (
            Vendor::Apple,
            OperatingSystem::Darwin(None),
            Environment::Unknown,
            BinaryFormat::Macho,
        ),
    };
    Triple {
        architecture: Architecture::Aarch64(Aarch64Architecture::Aarch64),
        vendor,
        operating_system,
        environment,
        binary_format,
    }
}

pub struct Setting {
    pub name: String,
    pub value: String,
}

pub enum CompileFailure {
    Parse,
    FunctionCount,
    SharedSetting,
    IsaSetting,
    Codegen(CodegenError),
}

pub struct Artifact {
    pub code: Vec<u8>,
    pub relocs: Vec<FinalizedMachReloc>,
    pub traps: Vec<MachTrap>,
    pub alignment: u32,
    /// The post-compile function (`params` and `name` resolve relocation targets).
    pub func: Function,
}

pub fn compile_aarch64(
    clif: &str,
    target: TargetSpec,
    flags: &[Setting],
    isa_flags: &[Setting],
) -> Result<Artifact, CompileFailure> {
    let mut funcs = cranelift_reader::parse_functions(clif).map_err(|_| CompileFailure::Parse)?;
    if funcs.len() != 1 {
        return Err(CompileFailure::FunctionCount);
    }
    let func = funcs.remove(0);

    let mut b = settings::builder();
    for s in flags {
        b.set(&s.name, &s.value)
            .map_err(|_| CompileFailure::SharedSetting)?;
    }
    let shared = settings::Flags::new(b);

    let mut ib = aarch64::settings::builder();
    for s in isa_flags {
        ib.set(&s.name, &s.value)
            .map_err(|_| CompileFailure::IsaSetting)?;
    }
    let isa_flags = aarch64::settings::Flags::new(&shared, &ib);

    let backend = AArch64Backend::new_with_flags(triple(target), shared, isa_flags);

    let mut ctx = Context::for_function(func);
    let compiled = ctx
        .compile(&backend, &mut ControlPlane::default())
        .map_err(|e| CompileFailure::Codegen(e.inner))?;
    // `write_code` in cranelift/filetests/src/artifact_export.rs.
    let alignment = compiled
        .buffer
        .alignment
        .max(backend.function_alignment().minimum)
        .max(<dyn TargetIsa>::symbol_alignment(&backend) as u32);
    let code = compiled.code_buffer().to_vec();
    let relocs = compiled.buffer.relocs().to_vec();
    let traps = compiled.buffer.traps().to_vec();
    Ok(Artifact {
        code,
        relocs,
        traps,
        alignment,
        func: ctx.func,
    })
}
