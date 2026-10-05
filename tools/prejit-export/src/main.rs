//! Cross-host export of the pinned stock filetest compiler's pre-JIT artifacts.
use anyhow::{Context, Result, bail};
use cranelift_codegen::{isa, settings::Configurable};
use cranelift_reader::{IsaSpec, ParseOptions};
use serde_json::json;
use std::{path::Path, str::FromStr};

fn run() -> Result<()> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() < 3
        || args[3..]
            .iter()
            .any(|s| s != "--stock-load" && s != "--all-stages")
    {
        bail!("usage: prejit-export INPUT OUT TARGET [--stock-load] [--all-stages]");
    }
    let (input, out, triple) = (
        &args[0],
        Path::new(&args[1]),
        target_lexicon::Triple::from_str(&args[2])?,
    );
    let stock_load = args[3..].iter().any(|s| s == "--stock-load");
    let all_stages = args[3..].iter().any(|s| s == "--all-stages");
    if stock_load && triple != target_lexicon::Triple::host() {
        bail!("--stock-load requires the host triple");
    }
    std::fs::create_dir_all(out)?;
    let source = std::fs::read_to_string(input)?;
    let test = match cranelift_reader::parse_test(
        &source,
        ParseOptions {
            machine_code_cfg_info: true,
            ..Default::default()
        },
    ) {
        Ok(test) => test,
        Err(e) if all_stages => {
            std::fs::write(
                out.join("manifest.json"),
                serde_json::to_vec_pretty(
                    &json!({"input":input,"parse_error":e.to_string(),"parse_error_is_warning":e.is_warning,"variants":[],"commands":[],"declared_targets":[],"actual_ci_execution":false}),
                )?,
            )?;
            return Ok(());
        }
        Err(e) => return Err(anyhow::anyhow!("{e}")),
    };
    let names: Vec<_> = test
        .functions
        .iter()
        .map(|(f, _)| f.name.to_string())
        .collect();
    let has_run = test.commands.iter().any(|c| c.command == "run");
    if all_stages {
        let mut variants = Vec::new();
        let mut declared_targets = Vec::new();
        if let IsaSpec::Some(isas) = &test.isa_spec {
            for (isa_index, requested) in isas.iter().enumerate() {
                declared_targets.push(json!({"isa_index":isa_index,"target":requested.triple().to_string(),"architecture":requested.triple().architecture.to_string(),"lean_architecture_supported":requested.triple().architecture == triple.architecture}));
                if requested.triple().architecture != triple.architecture {
                    continue;
                }
                for (command_index, command) in test.commands.iter().enumerate() {
                    if command.command != "run" && command.command != "compile" {
                        continue;
                    }
                    let isa = if command.command == "run" {
                        let mut builder = isa::lookup(triple.clone())?;
                        for value in requested.isa_flags() {
                            builder.set(value.name, &value.value_string())?;
                        }
                        builder.finish(requested.flags().clone())?
                    } else {
                        requested.clone()
                    };
                    let index = variants.len();
                    let directory = out.join(format!("variant-{index}"));
                    let flags: Vec<_> = isa
                        .flags()
                        .iter()
                        .map(|s| json!({"name":s.name,"value":s.value_string()}))
                        .collect();
                    let isa_flags: Vec<_> = isa
                        .isa_flags()
                        .iter()
                        .map(|s| json!({"name":s.name,"value":s.value_string()}))
                        .collect();
                    let eligible = command.command != "run" || !isa.flags().enable_pinned_reg();
                    let result = if eligible {
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            if command.command == "compile" {
                                cranelift_filetests::artifact_export::export_compile(
                                    &test, command, &*isa, &directory, input,
                                )
                            } else {
                                if !command.options.is_empty() {
                                    bail!("stock run accepts no command options");
                                }
                                for (func, _) in &test.functions {
                                    cranelift_codegen::verify_function(func, &*isa)
                                        .map_err(|e| anyhow::anyhow!("stock verifier: {e}"))?;
                                }
                                cranelift_filetests::function_runner::export_prejit(
                                    &test,
                                    isa.clone(),
                                    &directory,
                                    stock_load,
                                )
                            }
                        }))
                        .map_err(|_| anyhow::anyhow!("compiler panicked"))
                        .and_then(|r| r)
                    } else {
                        Err(anyhow::anyhow!("stock run excludes pinned_reg"))
                    };
                    variants.push(json!({"index":index,"isa_index":isa_index,"command_index":command_index,"stage":command.command,"command":command.to_string(),
                        "requested_target":requested.triple().to_string(),"target":isa.triple().to_string(),"flags":flags,"isa_flags":isa_flags,"functions":names,
                        "eligible":eligible,"status":if result.is_ok(){"exported"}else{"reference_error"},"error":result.err().map(|e|format!("{e:#}")),
                        "stock_load":stock_load,"feature_requirements":test.features.iter().map(|f|format!("{f:?}")).collect::<Vec<_>>() }));
                }
            }
        }
        std::fs::write(
            out.join("manifest.json"),
            serde_json::to_vec_pretty(
                &json!({"input":input,"target":triple.to_string(),"has_run_command":has_run,"functions":names,
            "commands":test.commands.iter().map(|c|c.to_string()).collect::<Vec<_>>(),"declared_targets":declared_targets,"variants":variants,
            "missing_required_isa":matches!(&test.isa_spec,IsaSpec::None(_)) && test.commands.iter().any(|c|c.command=="run"||c.command=="compile"),
            "mode":"all-stock-binary-stages-cross-host-compile-only","cpu_feature_compatibility_checked":false,"actual_ci_execution":false,
            "host_address_substitution_present":source.contains("__cranelift_throw")}),
            )?,
        )?;
        return Ok(());
    }
    let mut variants = Vec::new();
    let candidates = match &test.isa_spec {
        IsaSpec::None(flags) => vec![isa::lookup(triple.clone())?.finish(flags.clone())?],
        IsaSpec::Some(isas) => isas
            .iter()
            .filter(|i| i.triple().architecture == triple.architecture)
            .map(|i| {
                // Stock test_run copies requested ISA flags into a host-OS ISA.
                // Here Linux AArch64 substitutes for that host, without CPU inference.
                let mut builder = isa::lookup(triple.clone())?;
                for value in i.isa_flags() {
                    builder.set(value.name, &value.value_string())?;
                }
                builder
                    .finish(i.flags().clone())
                    .map_err(anyhow::Error::from)
            })
            .collect::<Result<Vec<_>>>()?,
    };
    for (index, isa) in candidates.into_iter().enumerate() {
        let directory = out.join(format!("variant-{index}"));
        let flags: Vec<_> = isa
            .flags()
            .iter()
            .map(|s| json!({"name":s.name,"value":s.value_string()}))
            .collect();
        let isa_flags: Vec<_> = isa
            .isa_flags()
            .iter()
            .map(|s| json!({"name":s.name,"value":s.value_string()}))
            .collect();
        let eligible = has_run && !isa.flags().enable_pinned_reg();
        let result = if eligible {
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                for (func, _) in &test.functions {
                    cranelift_codegen::verify_function(func, &*isa)
                        .map_err(|e| anyhow::anyhow!("stock verifier: {e}"))?;
                }
                cranelift_filetests::function_runner::export_prejit(
                    &test, isa, &directory, stock_load,
                )
            }))
            .map_err(|_| anyhow::anyhow!("compiler panicked"))
            .and_then(|r| r)
        } else {
            Err(anyhow::anyhow!(
                "stock run excludes pinned_reg or file has no test run"
            ))
        };
        variants.push(json!({"index":index,"target":triple.to_string(),"flags":flags,"isa_flags":isa_flags,
            "functions":names,"eligible":eligible,"status":if result.is_ok(){"exported"}else{"reference_error"},
            "error":result.err().map(|e|format!("{e:#}")),"stock_load":stock_load,
            "feature_requirements": test.features.iter().map(|f| match f {
                cranelift_reader::Feature::With(s)=>format!("{s}"),
                cranelift_reader::Feature::Without(s)=>format!("!{s}"),
            }).collect::<Vec<_>>() }));
    }
    std::fs::write(
        out.join("manifest.json"),
        serde_json::to_vec_pretty(&json!({"input":input,"target":triple.to_string(),
        "has_run_command":has_run,"functions":names,"variants":variants,
        "mode":if stock_load{"stock-load-validation"}else{"cross-host-compile-only"},
        "cpu_feature_compatibility_checked": false,"actual_ci_execution":false,
        "host_address_substitution_present":source.contains("__cranelift_throw")}))?,
    )
    .context("writing manifest")?;
    Ok(())
}
fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("prejit-export: {e:#}");
            std::process::ExitCode::FAILURE
        }
    }
}
