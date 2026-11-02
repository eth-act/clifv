"""Read Lean axiom reports without joining separate report lines."""
import re

HEADER = re.compile(r"^'(.+)' (does not depend on any axioms|depends on axioms:\s*\[.*)$")

def parse_records(output):
    records = []
    pending = None
    for raw in output.splitlines():
        line = raw.strip()
        match = HEADER.fullmatch(line)
        if match:
            if pending is not None:
                raise ValueError(f"Unclosed axiom report before {match.group(1)}")
            name, report = match.groups()
            if report == "does not depend on any axioms":
                records.append((name, []))
                continue
            pending = (name, report.split("[", 1)[1])
        elif pending is not None:
            pending = (pending[0], pending[1] + " " + line)
        else:
            continue
        name, body = pending
        if "]" in body:
            values, rest = body.split("]", 1)
            if rest.strip():
                raise ValueError(f"Unexpected text after axiom report for {name}")
            records.append((name, [x.strip() for x in values.split(",") if x.strip()]))
            pending = None
    if pending is not None:
        raise ValueError(f"Unclosed axiom report for {pending[0]}")
    return records
