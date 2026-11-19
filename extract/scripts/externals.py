#!/usr/bin/env python3
"""Generate ClifvGen/{TypesExternal,FunsExternal}.lean from the Aeneas templates.

Every external item of a template (one `axiom` per item, with its doc comment and attributes)
is kept unless a handwritten model under extract/lean/Models/ClifvModels/{Types,Funs}/ defines
the same name; the generated file imports those model modules. So the generated code always
builds. The unmodeled types stay axioms; the unmodeled functions become `opaque`s whose
(compiled) implementation fails with `Error.undef`, so that the extracted code is executable
and reaching an unmodeled function is a distinguishable runtime failure.

Usage: externals.py GENERATED_DIR   (the Aeneas `-dest` directory, containing ClifvGen/)
Prints a JSON summary: {"types": {"modeled": n, "axioms": [...]}, "funs": {...}}.
"""
import json
import re
import sys
from pathlib import Path

MODELS = Path(__file__).resolve().parent.parent / "lean" / "Models"
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:def|abbrev|structure|inductive|class|opaque|axiom|instance)\s+([^\s:({\[]+)"
)


def modeled_names(kind):
    """Names defined by the model modules of `kind` ("Types" or "Funs"), and those modules."""
    names, modules = set(), []
    for f in sorted((MODELS / "ClifvModels" / kind).rglob("*.lean")):
        modules.append(".".join(f.relative_to(MODELS).with_suffix("").parts))
        namespaces = []
        for line in f.read_text().splitlines():
            if m := re.match(r"^namespace\s+(\S+)", line):
                namespaces.append(m.group(1))
            elif re.match(r"^end\s+\S+", line) and namespaces:
                namespaces.pop()
            elif m := DECL.match(line):
                names.add(".".join(namespaces + [m.group(1).removeprefix("_root_.")]))
    return names, modules

def generate(template: Path, out: Path, kind: str):
    lines = template.read_text().splitlines()
    first = next(i for i, l in enumerate(lines) if l.startswith("/--"))
    header, body = lines[:first], lines[first:]
    # Items: a doc comment, attributes, then `axiom NAME ...` (NAME possibly on the next line).
    is_axiom = lambda l: l == "axiom" or l.startswith("axiom ")
    items, cur = [], []
    for l in body:
        if l.startswith("/--") and any(is_axiom(x) for x in cur):
            items.append(cur)
            cur = []
        cur.append(l)
    if cur:
        items.append(cur)
    names, modules = modeled_names(kind)
    kept, modeled = [], 0
    for item in items:
        i = next(i for i, l in enumerate(item) if is_axiom(l))
        name = " ".join(item[i : i + 2]).split()[1]
        if name in names:
            modeled += 1
        else:
            kept.append((name, item))
    if kind == "Funs":
        for _, item in kept:
            i = next(i for i, l in enumerate(item) if is_axiom(l))
            item[i] = "opaque" + item[i][len("axiom"):]
    imp = max(i for i, l in enumerate(header) if l.startswith("public import"))
    header = header[: imp + 1] + [f"public import {m}" for m in modules] + header[imp + 1 :]
    header = [l for l in header if not l.startswith("-- This is a template file")]
    if kind == "Funs":
        header += [
            "/-- The implementation of the functions without a model: fail with `undef`. -/",
            "local instance (priority := high) unmodeled (α : Type _) : Inhabited (Result α) :=",
            "  ⟨fail .undef⟩",
            "",
        ]
    text = "\n".join(header) + "\n" + "\n".join(l for _, item in kept for l in item) + "\n"
    out.write_text(text)
    return {"modeled": modeled, "axioms": [n for n, _ in kept]}


def main():
    gen = Path(sys.argv[1]) / "ClifvGen"
    summary = {}
    for kind in ("Types", "Funs"):
        template = gen / f"{kind}External_Template.lean"
        if template.exists():
            summary[kind.lower()] = generate(template, gen / f"{kind}External.lean", kind)
    json.dump(summary, sys.stdout)


if __name__ == "__main__":
    main()
