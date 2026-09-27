//! Loading the aarch64 ISLE compilation unit exactly as Cranelift builds it.
//!
//! 1. `cranelift_codegen_meta::generate_isle` writes the generated ISLE inputs
//!    (`numerics.isle`, `clif_lower.isle`, `clif_opt.isle`, `assembler.isle`)
//!    into a directory. This is the function the VeriISLE CLI calls; Cranelift's
//!    `build.rs` calls `meta::generate`, which runs the same ISLE generators.
//! 2. `cranelift_codegen_meta::isle::get_isle_compilations(..).lookup("aarch64")`
//!    gives the input list. With the meta crate's `spec` feature (enabled in our
//!    Cargo.toml) the list includes the VeriISLE spec files, as for VeriISLE.
//! 3. The files are lexed and parsed with `cranelift_isle`, and analysed with
//!    `TypeEnv::from_ast` / `TermEnv::from_ast(.., expand_internal_extractors =
//!    true)` followed by the overlap and recursion checks, as in
//!    `cranelift_isle::compile::compile`.

use anyhow::{Context, Result, anyhow, bail};
use cranelift_isle::{
    ast, codegen::Prefix, error::Errors, files::Files, lexer::Lexer, overlap, parser, recursion,
    sema,
};
use std::path::{Path, PathBuf};
use std::sync::Arc;

pub struct Unit {
    pub files: Arc<Files>,
    pub defs: Vec<ast::Def>,
    /// The analysed program, as `cranelift_isle::compile::compile` sees it.
    pub tyenv: sema::TypeEnv,
    pub termenv: sema::TermEnv,
}

impl Unit {
    pub fn sym(&self, s: sema::Sym) -> &str {
        &self.tyenv.syms[s.index()]
    }

    pub fn file_name(&self, file: usize) -> &str {
        self.files.file_name(file).unwrap()
    }

    /// 1-based line of a position.
    pub fn line(&self, pos: cranelift_isle::lexer::Pos) -> usize {
        self.files.file_line_map(pos.file).unwrap().line(pos.offset) + 1
    }
}

/// Generate the build-time ISLE inputs into `gen_dir` and return the ordered
/// input paths of the `aarch64` compilation.
///
/// Directory inputs (only `src/isa/aarch64/spec`, present because of the `spec`
/// feature) are expanded to their `.isle` files in sorted order; upstream uses
/// `read_dir` order, which is filesystem dependent. Declaration order does not
/// affect the rules, only the numbering of spec-only definitions.
pub fn input_paths(codegen_dir: &Path, gen_dir: &Path) -> Result<Vec<PathBuf>> {
    std::fs::create_dir_all(gen_dir)
        .with_context(|| format!("creating {}", gen_dir.display()))?;
    cranelift_codegen_meta::generate_isle(gen_dir)
        .map_err(|e| anyhow!("cranelift-codegen-meta generate_isle: {e}"))?;
    let comps = cranelift_codegen_meta::isle::get_isle_compilations(codegen_dir, gen_dir);
    let comp = comps
        .lookup("aarch64")
        .ok_or_else(|| anyhow!("no aarch64 ISLE compilation"))?;
    let mut out = Vec::new();
    for input in comp.inputs() {
        if input.is_dir() {
            let mut entries: Vec<PathBuf> = std::fs::read_dir(&input)
                .with_context(|| format!("reading {}", input.display()))?
                .map(|e| e.map(|e| e.path()))
                .collect::<std::io::Result<_>>()?;
            entries.retain(|p| p.extension().is_some_and(|e| e == "isle"));
            entries.sort();
            out.extend(entries);
        } else if input.is_file() {
            out.push(input);
        } else {
            bail!("ISLE input does not exist: {}", input.display());
        }
    }
    Ok(out)
}

pub fn load(codegen_dir: &Path, gen_dir: &Path) -> Result<Unit> {
    let paths = input_paths(codegen_dir, gen_dir)?;
    // Display names as in Cranelift's generated code: codegen-crate-relative
    // (`src/isa/aarch64/lower.isle`) and `<OUT_DIR>/clif_lower.isle`.
    let prefixes = [
        Prefix {
            prefix: format!("{}/", codegen_dir.display()),
            name: String::new(),
        },
        Prefix {
            prefix: gen_dir.display().to_string(),
            name: "<OUT_DIR>".to_string(),
        },
    ];
    let files = Files::from_paths(&paths, &prefixes)
        .map_err(|(p, e)| anyhow!("cannot read {}: {e}", p.display()))?;
    let files = Arc::new(files);

    let mut defs = Vec::new();
    for (file, src) in files.file_texts.iter().enumerate() {
        let lexer = Lexer::new(file, src).map_err(|e| errs(vec![e], &files))?;
        let mut ds = parser::parse(lexer).map_err(|e| errs(vec![e], &files))?;
        defs.append(&mut ds);
    }

    let mut tyenv = sema::TypeEnv::from_ast(&defs).map_err(|e| errs(e, &files))?;
    let termenv =
        sema::TermEnv::from_ast(&mut tyenv, &defs, true).map_err(|e| errs(e, &files))?;
    // The checks `compile::compile` runs before codegen: the unit must be one
    // Cranelift accepts.
    let terms = overlap::check(&termenv).map_err(|e| errs(e, &files))?;
    recursion::check(&terms, &termenv).map_err(|e| errs(e, &files))?;

    Ok(Unit {
        files,
        defs,
        tyenv,
        termenv,
    })
}

fn errs(e: Vec<cranelift_isle::error::Error>, files: &Arc<Files>) -> anyhow::Error {
    anyhow!("{}", Errors::new(e, files.clone()))
}
