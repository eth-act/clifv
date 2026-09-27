//! `; run:` / `; print:` handling and the JSON result schema shared by `clif-oracle`
//! (Cranelift interpreter) and `clif-native` (native aarch64 execution). The schema is
//! specified in `docs/contracts/clif.md`; one record per run command, in file order.

use cranelift_codegen::data_value::DataValue;
use cranelift_codegen::ir::Function;
use cranelift_reader::{Comparison, Details, RunCommand, parse_run_command};
use serde_json::{Value, json};

/// `{"ty": "i32", "bits": "0x0000002a"}`: the value's bytes as a little-endian unsigned
/// number, zero-padded to the type's width.
pub fn value_json(v: &DataValue) -> Value {
    let ty = v.ty();
    let n = ty.bytes() as usize;
    let mut buf = vec![0u8; n];
    v.write_to_slice_le(&mut buf);
    let hex: String = buf.iter().rev().map(|b| format!("{b:02x}")).collect();
    json!({ "ty": ty.to_string(), "bits": format!("0x{hex}") })
}

pub fn values_json(vs: &[DataValue]) -> Value {
    Value::Array(vs.iter().map(value_json).collect())
}

/// Function name without the leading `%` (testcase names) or its display form.
pub fn plain_name(f: &Function) -> String {
    let s = f.name.to_string();
    s.strip_prefix('%').map(str::to_string).unwrap_or(s)
}

/// One `; run`/`; print` comment of a function.
pub struct RunLine {
    /// The function the comment follows.
    pub attached: String,
    /// The invoked function (a bare `; run` invokes the attached function).
    pub func: String,
    pub args: Vec<DataValue>,
    /// `{"cmp": "==" | "!=", "values": [...]}`, or `null` for `; print`.
    pub expected: Value,
    /// Set when the comment looks like a run command but does not parse; the record's
    /// `actual` is then this error and nothing is run.
    pub parse_error: Option<String>,
}

impl RunLine {
    /// The JSON record for this command with the given `actual` outcome.
    pub fn record(&self, actual: Value) -> Value {
        json!({
            "attached": self.attached,
            "func": self.func,
            "args": values_json(&self.args),
            "expected": self.expected,
            "actual": actual,
        })
    }

    /// The record for a command that was not run because it does not parse.
    pub fn parse_error_record(&self) -> Option<Value> {
        self.parse_error.as_ref().map(|e| self.record(json!({ "error": e })))
    }
}

/// The run commands in `details`' comments (attached to `func`), in order.
pub fn run_lines(func: &Function, details: &Details) -> Vec<RunLine> {
    let attached = plain_name(func);
    let mut out = Vec::new();
    for comment in &details.comments {
        let cmd = match parse_run_command(comment.text, &func.signature) {
            Ok(Some(cmd)) => cmd,
            Ok(None) => continue,
            Err(e) => {
                out.push(RunLine {
                    attached: attached.clone(),
                    func: attached.clone(),
                    args: Vec::new(),
                    expected: Value::Null,
                    parse_error: Some(format!("run command does not parse: {e}")),
                });
                continue;
            }
        };
        let (inv, expected) = match &cmd {
            RunCommand::Print(inv) => (inv, Value::Null),
            RunCommand::Run(inv, cmp, vals) => {
                let cmp = match cmp {
                    Comparison::Equals => "==",
                    Comparison::NotEquals => "!=",
                };
                (inv, json!({ "cmp": cmp, "values": values_json(vals) }))
            }
        };
        // A bare `; run` has the invocation name `default`: it means the attached function
        // (as in `test run`).
        let name = if inv.func == "default" { attached.clone() } else { inv.func.clone() };
        out.push(RunLine {
            attached: attached.clone(),
            func: name,
            args: inv.args.clone(),
            expected,
            parse_error: None,
        });
    }
    out
}
