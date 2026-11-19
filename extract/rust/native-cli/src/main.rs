//! Native reference for the extracted pipeline: same request/result schema as
//! `clifv-extract-lean`. Emits structure only; `extract/scripts/compare.py` renders
//! display strings once.
use anyhow::{Context, Result, bail};
use clifv_extract_entry::{CompileFailure, Setting, TargetSpec, compile_aarch64, triple};
use cranelift_codegen::FinalizedRelocTarget;
use cranelift_codegen::ir::{ExternalName, Function, UserFuncName};
use serde_json::{Value, json};
use std::str::FromStr;

fn spec(name: &str) -> Result<TargetSpec> {
    Ok(match name {
        "Aarch64UnknownUnknown" => TargetSpec::Aarch64UnknownUnknown,
        "Aarch64UnknownUnknownElf" => TargetSpec::Aarch64UnknownUnknownElf,
        "Aarch64UnknownLinuxGnu" => TargetSpec::Aarch64UnknownLinuxGnu,
        "Aarch64AppleDarwin" => TargetSpec::Aarch64AppleDarwin,
        _ => bail!("unknown target_spec {name}"),
    })
}

fn settings(v: &Value) -> Result<Vec<Setting>> {
    v.as_array()
        .context("settings must be an array")?
        .iter()
        .map(|s| {
            Ok(Setting {
                name: s["name"].as_str().context("setting name")?.to_string(),
                value: s["value"].as_str().context("setting value")?.to_string(),
            })
        })
        .collect()
}

fn testcase(raw: &[u8]) -> String {
    String::from_utf8(raw.to_vec()).expect("testcase names are UTF-8 (stock Display unwraps)")
}

fn func_name(func: &Function) -> Value {
    match &func.name {
        UserFuncName::User(u) => json!({"user":[u.namespace,u.index]}),
        UserFuncName::Testcase(t) => json!({"testcase":testcase(t.raw())}),
    }
}

fn target(func: &Function, t: &FinalizedRelocTarget) -> Value {
    match t {
        FinalizedRelocTarget::Func(offset) => json!({"func_offset":offset}),
        FinalizedRelocTarget::ExternalName(name) => match name {
            ExternalName::User(r) => {
                let u = &func.params.user_named_funcs()[*r];
                json!({"user":[u.namespace,u.index]})
            }
            ExternalName::TestCase(t) => json!({"testcase":testcase(t.raw())}),
            ExternalName::LibCall(lc) => json!({"libcall":format!("{lc:?}")}),
            ExternalName::KnownSymbol(ks) => json!({"known_symbol":format!("{ks:?}")}),
        },
    }
}

fn run(request: &Value) -> Result<Value> {
    if request["schema"] != 1 {
        bail!("unsupported request schema");
    }
    let target_str = request["target"].as_str().context("target")?;
    let spec_name = request["target_spec"].as_str().context("target_spec")?;
    if triple(spec(spec_name)?) != target_lexicon::Triple::from_str(target_str).map_err(|e| anyhow::anyhow!("{e}"))? {
        return Ok(json!({"schema":1,"status":"error","reason":"target_spec_mismatch"}));
    }
    let clif = std::fs::read_to_string(request["clif_path"].as_str().context("clif_path")?)?;
    let flags = settings(&request["flags"])?;
    let isa_flags = settings(&request["isa_flags"])?;
    let artifact = match compile_aarch64(&clif, spec(spec_name)?, &flags, &isa_flags) {
        Ok(a) => a,
        Err(f) => {
            let stage = match f {
                CompileFailure::Parse => "parse",
                CompileFailure::FunctionCount => "function_count",
                CompileFailure::SharedSetting => "shared_setting",
                CompileFailure::IsaSetting => "isa_setting",
                CompileFailure::Codegen(_) => "codegen",
            };
            return Ok(json!({"schema":1,"status":"rejected","stage":stage}));
        }
    };
    let code_hex: String = artifact.code.iter().map(|b| format!("{b:02x}")).collect();
    let relocs: Vec<_> = artifact
        .relocs
        .iter()
        .map(|r| {
            json!({"offset":r.offset,"kind":format!("{:?}",r.kind),
                   "target":target(&artifact.func,&r.target),"addend":r.addend})
        })
        .collect();
    let traps: Vec<_> = artifact
        .traps
        .iter()
        .map(|t| json!({"offset":t.offset,"code":t.code.as_raw().get()}))
        .collect();
    Ok(json!({"schema":1,"status":"compiled","code_hex":code_hex,"alignment":artifact.alignment,
              "func_name":func_name(&artifact.func),"relocs":relocs,"traps":traps}))
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 2 {
        bail!("usage: clifv-extract-native REQUEST.json RESULT.json");
    }
    let request: Value = serde_json::from_slice(&std::fs::read(&args[0])?)?;
    let result = run(&request)?;
    std::fs::write(&args[1], serde_json::to_vec(&result)?)?;
    Ok(())
}
