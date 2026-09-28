#!/usr/bin/env python3
"""Generates `FV/Opt/Proof/RuleCtor.lean` from the source of `Isle.Opt.ctorPure`.

usage: python3 FVTest/Opt/Proof/gen_ctor.py > FV/Opt/Proof/RuleCtor.lean

Untrusted: every emitted lemma is proven by `rfl`, so Lean checks that it is the definition.
For each arm `| "fn", [a, b] => body` of `ctorPure` (FV/Isle/Opt/Simplify.lean) it emits

    @[opt_monad] theorem ctorFn_fn (G : EGraph σ) ... (st : St σ) :
        ctorFn G "fn" [args] st = ((do body') : R (Option V)) >>= fun o => pure (o.map (·, st))

where an argument read as `(← a.ty?)` / `(← a.int?)` is bound as `.ty a` / `.int a` (so the
`← a.ty?` disappear), and the local shorthands `ok`/`int`/`bool`/`opt` are expanded.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SRC = (ROOT / "FV/Isle/Opt/Simplify.lean").read_text()

start = SRC.index("def ctorPure")
end = SRC.index("def ctorFn")
lines = SRC[start:end].splitlines()

# Collect arms: a line starting with `  | "` begins an arm; following lines indented by at
# least 4 spaces continue it.
arms = []
for ln in lines:
    m = re.match(r'  \| "([^"]+)", \[(.*)\] => ?(.*)$', ln)
    if m:
        arms.append([m.group(1), m.group(2), [m.group(3)] if m.group(3) else []])
    elif arms and ln.startswith("    ") and not ln.strip().startswith("--"):
        arms[-1][2].append(ln[4:])
    elif ln.startswith("  --") or ln.startswith("  | _, _"):
        continue


def expand(body: str, name: str, arg: str) -> str:
    """Replace `name X` (X one parenthesised expression or one identifier path) by the
    expansion of the shorthand."""
    out = []
    i = 0
    pat = re.compile(r'(?<![\w.])' + name + r' ')
    while True:
        m = pat.search(body, i)
        if not m:
            out.append(body[i:])
            break
        out.append(body[i:m.start()])
        j = m.end()
        if body[j] == "(":
            depth = 0
            k = j
            while True:
                if body[k] == "(":
                    depth += 1
                elif body[k] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                k += 1
            x = body[j:k + 1]
            i = k + 1
        else:
            m2 = re.match(r"[\w.'?]+", body[j:])
            x = m2.group(0)
            i = j + len(x)
        out.append(arg.replace("X", x))
    return "".join(out)


V_CTORS = {
    "jumpTable": ["Clif.BlockCall", "List Clif.BlockCall"],
    "blockCall": ["Clif.BlockCall"],
}

print("""import FV.Isle.Opt.Simplify
import FV.Opt.Proof.RuleAttr

/-!
# The extern constructors of `ctorPure`, one `rfl` lemma each (generated, do not edit)

Regenerate: `python3 FVTest/Opt/Proof/gen_ctor.py > FV/Opt/Proof/RuleCtor.lean`.

`ctorFn G "fn" args st` for a literal `fn` only reduces by `rfl` (string-literal matches), so
the forward evaluation of right-hand sides (`opt_eval`) rewrites with these lemmas
(`opt_monad`). The right-hand side is the arm of `ctorPure` with the arguments bound to their
constructors (`.ty t`, `.int x`) and the shorthands `ok`/`int`/`bool`/`opt` expanded; the
helper specifications (`FV/Opt/Proof/RuleImm.lean`) then compute the Rust helper.
-/

set_option linter.unusedVariables false

namespace Opt.Proof

open Isle Isle.Opt

section
variable {σ : Type} (G : EGraph σ)
""")

for fn, argsrc, body in arms:
    text = "\n".join(body)
    args = [a.strip() for a in argsrc.split(",")] if argsrc.strip() else []
    binders = []
    pats = []
    # Constructor patterns in the argument list (`.jumpTable d tbl`).
    for a in args:
        m = re.match(r"\.(\w+) (.*)$", a)
        if m:
            ctor, vs = m.group(1), m.group(2).split()
            for v, ty in zip(vs, V_CTORS[ctor]):
                binders.append(f"({v} : {ty})")
            pats.append(a)
            continue
        v = a
        if f"(← {v}.ty?)" in text:
            binders.append(f"({v} : CTy)")
            pats.append(f".ty {v}")
            text = text.replace(f"(← {v}.ty?)", v)
        elif f"(← {v}.int?)" in text or f"← {v}.int?" in text:
            binders.append(f"({v} : Int)")
            pats.append(f".int {v}")
            text = text.replace(f"(← {v}.int?)", v).replace(f"{{← {v}.int?}}", f"{{{v}}}")
            text = re.sub(rf"(?m)^let {v} ← {v}\.int\?\n", "", text)
        else:
            binders.append(f"({v} : V)")
            pats.append(v)
    text = expand(text, "int", "pure (some (V.int X))")
    text = expand(text, "bool", "pure (some (V.bool X))")
    text = expand(text, "opt", "pure (Option.map V.int X)")
    text = expand(text, "ok", "pure (some X)")
    body_lines = text.splitlines()
    if body_lines and body_lines[0].strip() == "do":
        body_lines = body_lines[1:]
    ident = re.sub(r"\W", "_", fn)
    ind = "        "
    rhs = "\n".join(ind + b for b in body_lines)
    print(f"@[opt_monad] theorem ctorFn_{ident} {' '.join(binders)} (st : St σ) :")
    print(f"    ctorFn G {fn!r} [{', '.join(pats)}] st =".replace("'", '"'))
    print(f"      ((do\n{rhs}\n      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl")
    print()

print("""end

end Opt.Proof""")
