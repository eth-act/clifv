//! Rules of the mid-end roots `simplify` / `simplify_skeleton` that can fire on
//! programs of the emitter subset E (`clif-subset-v2`, `closure::E_OPCODES`) at
//! `i8`..`i64`.
//!
//! Root selection is the aarch64 closure's syntactic test (`closure.rs`), with an
//! opcode set as parameter: a root rule is dropped iff its main LHS (the
//! arguments of `simplify`, which include every nested `inst_data_value` node
//! pattern) mentions an `Opcode.X` outside the set, a `Type` constant other than
//! `$I8 $I16 $I32 $I64`, or an extern `Type` extractor that fails on scalar
//! integers (`NON_SCALAR_INT` plus the mid-end's `ty_vector`, `ty_int_vec128`).
//!
//! Rewrites add nodes to the e-graph, and those can have opcodes outside E (for
//! example `bmask`, `iabs`, `rotl`). So the opcode set is closed under the
//! opcodes that the right-hand sides of selected root rules can build
//! (`Opcode.X` constructed in the RHS or if-let expressions, transitively through
//! internal constructors; dependency rules whose LHS names a non-E type are
//! skipped, a hint rather than a proof), to a fixed point `E*`. The closure is
//! computed at `E*`; `eRootRules` lists the root rules that already match with
//! E opcodes only. Dependencies (every rule of every internal-constructor term a
//! closure rule mentions) are added transitively without filtering, as for
//! aarch64.

use crate::closure::{self, Atom, E_OPCODES, NON_SCALAR_INT, camel, lopt, lstrs, pat_terms};
use crate::lean::lstr;
use crate::load::Unit;
use anyhow::{Result, anyhow};
use cranelift_isle::ast;
use cranelift_isle::sema::{self, RuleId, TermId, TermKind};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write;
use std::path::Path;

pub const ROOTS: &[&str] = &["simplify", "simplify_skeleton"];

/// Mid-end extern `Type` extractors that fail on `i8`..`i64` (`opts.rs` `ty_vector`,
/// `isle_prelude.rs` `ty_int_vec128`), in addition to `closure::NON_SCALAR_INT`.
pub const NON_SCALAR_INT_OPT: &[&str] = &["ty_vector", "ty_int_vec128"];

/// Rust sources of the mid-end's extern helpers (codegen-crate relative).
const RUST_SOURCES: &[&str] = &["src/opts.rs", "src/isle_prelude.rs"];

const TYPE_CONSTS_OK: &[&str] = closure::TYPE_CONSTS_OK;

fn non_scalar_int(name: &str) -> bool {
    NON_SCALAR_INT.contains(&name) || NON_SCALAR_INT_OPT.contains(&name)
}

/// Why the main LHS of `r` cannot match when every node has an opcode in `ops`.
fn lhs_reasons(u: &Unit, r: &sema::Rule, ops: &BTreeSet<String>) -> Vec<String> {
    let mut v = Vec::new();
    for a in &r.args {
        pat_terms(a, &mut v);
    }
    let mut reasons = BTreeSet::new();
    for a in v {
        let t = match a {
            Atom::Const(ty, sym) => {
                let tyname = u.tyenv.types[ty.index()].name(&u.tyenv);
                let name = u.sym(sym);
                if tyname == "Type" && !TYPE_CONSTS_OK.contains(&name) {
                    reasons.insert(name.to_string());
                }
                continue;
            }
            Atom::Term(t) => t,
        };
        let term = &u.termenv.terms[t.index()];
        let name = u.sym(term.name);
        match &term.kind {
            TermKind::EnumVariant { .. } => {
                if let Some(op) = name.strip_prefix("Opcode.") {
                    if !ops.contains(op) {
                        reasons.insert(name.to_string());
                    }
                }
            }
            TermKind::Decl { .. } => {
                if term.has_external_extractor() && non_scalar_int(name) {
                    reasons.insert(name.to_string());
                }
            }
            TermKind::Struct => {}
        }
    }
    reasons.into_iter().collect()
}

/// `Opcode.X` names (`X` in CamelCase) and internal terms constructed by an expression.
fn expr_ops(u: &Unit, e: &sema::Expr, ops: &mut BTreeSet<String>, terms: &mut BTreeSet<TermId>) {
    let mut ts = BTreeSet::new();
    closure::expr_terms(e, &mut ts);
    for t in ts {
        let term = &u.termenv.terms[t.index()];
        let name = u.sym(term.name);
        match &term.kind {
            TermKind::EnumVariant { .. } => {
                if let Some(op) = name.strip_prefix("Opcode.") {
                    ops.insert(op.to_string());
                }
            }
            TermKind::Decl { .. } if term.has_internal_constructor() => {
                terms.insert(t);
            }
            _ => {}
        }
    }
}

/// Opcodes the RHS and if-let expressions of root rule `r` can build, transitively through
/// internal constructors (other than the roots). Dependency rules whose LHS names a non-E
/// type are skipped.
fn rhs_ops(
    u: &Unit,
    r: &sema::Rule,
    rules_of: &HashMap<TermId, Vec<RuleId>>,
    roots: &[TermId],
    e_ops: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut ops = BTreeSet::new();
    let mut todo = BTreeSet::new();
    for il in &r.iflets {
        expr_ops(u, &il.rhs, &mut ops, &mut todo);
    }
    expr_ops(u, &r.rhs, &mut ops, &mut todo);
    let mut seen: HashSet<TermId> = roots.iter().copied().collect();
    while let Some(t) = todo.pop_first() {
        if !seen.insert(t) {
            continue;
        }
        for &r2 in rules_of.get(&t).map(|v| v.as_slice()).unwrap_or(&[]) {
            let rule = &u.termenv.rules[r2.index()];
            let why = lhs_reasons(u, rule, e_ops);
            if why.iter().any(|w| !w.starts_with("Opcode.")) {
                continue;
            }
            for il in &rule.iflets {
                expr_ops(u, &il.rhs, &mut ops, &mut todo);
            }
            expr_ops(u, &rule.rhs, &mut ops, &mut todo);
        }
    }
    ops
}

/// `file:line` of `fn <name>` (or `type <name>_returns`) in the helper sources.
fn rust_source(texts: &[(String, String)], name: &str) -> Option<String> {
    let pats = [format!("fn {name}("), format!("fn {name}<")];
    for (file, text) in texts {
        for (i, l) in text.lines().enumerate() {
            if pats.iter().any(|p| l.contains(p.as_str())) {
                return Some(format!("{file}:{}", i + 1));
            }
        }
    }
    None
}

pub fn render(u: &Unit, rule_names: &[String], header: &str, codegen_dir: &Path) -> Result<String> {
    let e_ops: BTreeSet<String> = E_OPCODES.iter().map(|o| camel(o)).collect();
    for op in &e_ops {
        let id = ast::Ident(format!("Opcode.{op}"), Default::default());
        u.termenv
            .get_term_by_name(&u.tyenv, &id)
            .ok_or_else(|| anyhow!("E opcode Opcode.{op} not found"))?;
    }
    let attrs = closure::attrs(u);
    let mut rules_of: HashMap<TermId, Vec<RuleId>> = HashMap::new();
    for r in &u.termenv.rules {
        rules_of.entry(r.root_term).or_default().push(r.id);
    }
    let mut roots = Vec::new();
    for name in ROOTS {
        let id = ast::Ident(name.to_string(), Default::default());
        roots.push(
            u.termenv
                .get_term_by_name(&u.tyenv, &id)
                .ok_or_else(|| anyhow!("root term {name} not found"))?,
        );
    }
    let root_rules: Vec<RuleId> = roots
        .iter()
        .flat_map(|t| rules_of.get(t).cloned().unwrap_or_default())
        .collect();

    // Fixed point of the opcode set under rewrite-introduced opcodes.
    let mut ops = e_ops.clone();
    let mut rounds = 0;
    let introduced_by: BTreeMap<RuleId, BTreeSet<String>> = loop {
        rounds += 1;
        let mut new_ops = ops.clone();
        let mut intro = BTreeMap::new();
        for &r in &root_rules {
            let rule = &u.termenv.rules[r.index()];
            if lhs_reasons(u, rule, &ops).is_empty() {
                let built: BTreeSet<String> = rhs_ops(u, rule, &rules_of, &roots, &e_ops)
                    .into_iter()
                    .filter(|o| !e_ops.contains(o))
                    .collect();
                new_ops.extend(built.iter().cloned());
                if !built.is_empty() {
                    intro.insert(r, built);
                }
            }
        }
        if new_ops == ops {
            break intro;
        }
        ops = new_ops;
    };
    let introduced: Vec<String> = ops.difference(&e_ops).cloned().collect();

    let mut in_closure: BTreeSet<RuleId> = BTreeSet::new();
    let mut excluded_roots: Vec<(RuleId, Vec<String>)> = Vec::new();
    let mut e_root_rules: Vec<RuleId> = Vec::new();
    let mut work: Vec<RuleId> = Vec::new();
    for &r in &root_rules {
        let rule = &u.termenv.rules[r.index()];
        let reasons = lhs_reasons(u, rule, &ops);
        if reasons.is_empty() {
            if lhs_reasons(u, rule, &e_ops).is_empty() {
                e_root_rules.push(r);
            }
            if in_closure.insert(r) {
                work.push(r);
            }
        } else {
            excluded_roots.push((r, reasons));
        }
    }
    let mut terms: BTreeSet<TermId> = roots.iter().copied().collect();
    let mut expanded: HashSet<TermId> = roots.iter().copied().collect();
    while let Some(r) = work.pop() {
        for t in closure::rule_terms(&u.termenv.rules[r.index()]) {
            terms.insert(t);
            if expanded.insert(t) && u.termenv.terms[t.index()].has_internal_constructor() {
                for &r2 in rules_of.get(&t).map(|v| v.as_slice()).unwrap_or(&[]) {
                    if in_closure.insert(r2) {
                        work.push(r2);
                    }
                }
            }
        }
    }

    let tags_of_term =
        |t: usize| -> BTreeSet<String> { attrs.term_tags.get(&t).cloned().unwrap_or_default() };

    let mut o = String::from(header);
    o.push_str(
        "import FV.Isle.Syntax\n\nset_option maxRecDepth 100000\n\nnamespace Isle.Opt.Closure\nopen Isle\n\n",
    );
    o.push_str(
        "/-! Rules and terms of the mid-end roots `simplify` / `simplify_skeleton` that can fire\n\
         on programs of the emitter subset E (`clif-subset-v2`) at `i8`..`i64`, with the opcode set\n\
         closed under the opcodes rewrites build (`opcodes ++ introducedOpcodes`); see\n\
         `docs/contracts/isle.md` (\"Mid-end export\"). -/\n\n",
    );
    let mut e_list: Vec<String> = E_OPCODES.iter().map(|s| s.to_string()).collect();
    e_list.sort();
    let _ = writeln!(o, "def opcodes : List String := {}\n", lstrs(&e_list));
    let _ = writeln!(
        o,
        "/-- Opcodes (ISLE `Opcode` variant names) outside E that rewrites of closure root rules\n\
         can build; the closure is computed with them admitted ({rounds} rounds to the fixed point). -/\n\
         def introducedOpcodes : List String := {}\n",
        lstrs(&introduced)
    );
    let roots_s: Vec<String> = ROOTS.iter().map(|s| s.to_string()).collect();
    let _ = writeln!(o, "def roots : List String := {}\n", lstrs(&roots_s));
    let de: Vec<String> = closure::DEFAULT_EXCLUDES.iter().map(|s| s.to_string()).collect();
    let _ = writeln!(o, "def defaultExcludes : List String := {}\n", lstrs(&de));
    let nsi: Vec<String> = NON_SCALAR_INT
        .iter()
        .chain(NON_SCALAR_INT_OPT)
        .map(|s| s.to_string())
        .collect();
    let _ = writeln!(o, "def nonScalarIntExtractors : List String := {}\n", lstrs(&nsi));

    // Rules.
    let mut n_excl = 0;
    let mut n_hint = 0;
    o.push_str(
        "/-- Closure rules: `⟨rule id, name, term id, isRoot, tags, defaultExcludedBy, lhsReasons⟩`\n\
         (`lhsReasons` against E opcodes only). -/\n\
         def rules : Array ClosureRule := #[\n",
    );
    let n = in_closure.len();
    for (i, r) in in_closure.iter().enumerate() {
        let rule = &u.termenv.rules[r.index()];
        let mut tags: BTreeSet<String> =
            attrs.rule_tags.get(&r.index()).cloned().unwrap_or_default();
        tags.extend(tags_of_term(rule.root_term.index()));
        for t in closure::rule_terms(rule) {
            tags.extend(tags_of_term(t.index()));
        }
        let excl: Vec<String> = tags
            .iter()
            .filter(|t| closure::DEFAULT_EXCLUDES.contains(&t.as_str()))
            .cloned()
            .collect();
        if !excl.is_empty() {
            n_excl += 1;
        }
        let reasons = lhs_reasons(u, rule, &e_ops);
        if !reasons.is_empty() {
            n_hint += 1;
        }
        let _ = writeln!(
            o,
            "  ⟨{}, {}, {}, {}, {}, {}, {}⟩{}",
            r.index(),
            lstr(&rule_names[r.index()]),
            rule.root_term.index(),
            if roots.contains(&rule.root_term) { "true" } else { "false" },
            lstrs(&tags),
            lstrs(&excl),
            lstrs(&reasons),
            if i + 1 < n { "," } else { "]" }
        );
    }
    if n == 0 {
        o.push_str("]\n");
    }

    let names = |rs: &mut dyn Iterator<Item = RuleId>| -> Vec<String> {
        rs.map(|r| rule_names[r.index()].clone()).collect()
    };
    let _ = writeln!(
        o,
        "\n/-- Root rules whose LHS matches with E opcodes only (no rewrite-introduced opcode). -/\n\
         def eRootRules : List String := {}",
        lstrs(&names(&mut e_root_rules.iter().copied()))
    );

    o.push_str(
        "\n/-- Closure root rules whose right-hand side can build opcodes outside E. -/\n\
         def introducingRules : Array (String × List String) := #[",
    );
    let ni = introduced_by.len();
    for (i, (r, built)) in introduced_by.iter().enumerate() {
        let b: Vec<String> = built.iter().cloned().collect();
        let _ = write!(
            o,
            "\n  ({}, {}){}",
            lstr(&rule_names[r.index()]),
            lstrs(&b),
            if i + 1 < ni { "," } else { "" }
        );
    }
    o.push_str("]\n");

    o.push_str(
        "\n/-- Root rules left out, with the LHS facts that rule them out (opcodes outside\n\
         `opcodes ++ introducedOpcodes`, non-E types). -/\n\
         def excludedRootRules : Array (String × List String) := #[\n",
    );
    for (i, (r, why)) in excluded_roots.iter().enumerate() {
        let _ = writeln!(
            o,
            "  ({}, {}){}",
            lstr(&rule_names[r.index()]),
            lstrs(why),
            if i + 1 < excluded_roots.len() { "," } else { "]" }
        );
    }
    if excluded_roots.is_empty() {
        o.push_str("]\n");
    }

    // Terms and extern helpers.
    let texts: Vec<(String, String)> = RUST_SOURCES
        .iter()
        .map(|f| {
            let t = std::fs::read_to_string(codegen_dir.join(f)).unwrap_or_default();
            (f.to_string(), t)
        })
        .collect();
    let mut n_ext_ctor = 0;
    let mut n_ext_ext = 0;
    let mut n_ext_spec = 0;
    let mut n_ext = 0;
    let mut sources: Vec<(String, Option<String>)> = Vec::new();
    o.push_str(
        "\n/-- Terms mentioned by closure rules:\n\
         `⟨term id, name, kind, extern constructor fn, extern extractor fn, has spec, chain, tags⟩`. -/\n\
         def terms : Array ClosureTerm := #[\n",
    );
    let nt = terms.len();
    for (i, t) in terms.iter().enumerate() {
        let term = &u.termenv.terms[t.index()];
        let kind = match &term.kind {
            TermKind::EnumVariant { .. } => ".enumVariant",
            TermKind::Struct => ".struct",
            TermKind::Decl { .. } => ".decl",
        };
        let ctor = match &term.kind {
            TermKind::Decl {
                constructor_kind: Some(sema::ConstructorKind::ExternalConstructor { name }),
                ..
            } => Some(u.sym(*name)),
            _ => None,
        };
        let ext = match &term.kind {
            TermKind::Decl {
                extractor_kind: Some(sema::ExtractorKind::ExternalExtractor { name, .. }),
                ..
            } => Some(u.sym(*name)),
            _ => None,
        };
        let spec = attrs.spec.contains(&t.index());
        if ctor.is_some() {
            n_ext_ctor += 1;
        }
        if ext.is_some() {
            n_ext_ext += 1;
        }
        if ctor.is_some() || ext.is_some() {
            n_ext += 1;
            if spec {
                n_ext_spec += 1;
            }
        }
        for f in ctor.iter().chain(ext.iter()) {
            sources.push((f.to_string(), rust_source(&texts, f)));
        }
        let _ = writeln!(
            o,
            "  ⟨{}, {}, {}, {}, {}, {}, {}, {}⟩{}",
            t.index(),
            lstr(u.sym(term.name)),
            kind,
            lopt(ctor),
            lopt(ext),
            if spec { "true" } else { "false" },
            if attrs.chain.contains(&t.index()) { "true" } else { "false" },
            lstrs(&tags_of_term(t.index())),
            if i + 1 < nt { "," } else { "]" }
        );
    }
    sources.sort();
    sources.dedup();
    o.push_str(
        "\n/-- Extern Rust functions of the closure's extern terms and where they are defined\n\
         (`none`: a macro-generated or trait-default method). -/\n\
         def rustSources : Array (String × Option String) := #[",
    );
    let ns = sources.len();
    for (i, (f, loc)) in sources.iter().enumerate() {
        let _ = write!(
            o,
            "\n  ({}, {}){}",
            lstr(f),
            lopt(loc.as_deref()),
            if i + 1 < ns { "," } else { "" }
        );
    }
    o.push_str("]\n");

    let _ = writeln!(
        o,
        "\n/-- Summary counts (also in `docs/contracts/isle.md`). -/\n\
         def summary : List (String × Nat) := [\n  \
         (\"rules\", {n}), (\"rootRules\", {}), (\"eRootRules\", {}), (\"excludedRootRules\", {}),\n  \
         (\"introducedOpcodes\", {}), (\"introducingRules\", {ni}),\n  \
         (\"rulesExcludedByDefaultTags\", {n_excl}), (\"rulesWithLhsReasons\", {n_hint}),\n  \
         (\"terms\", {nt}), (\"externTerms\", {n_ext}), (\"externConstructors\", {n_ext_ctor}),\n  \
         (\"externExtractors\", {n_ext_ext}), (\"externTermsWithSpec\", {n_ext_spec})]\n",
        in_closure
            .iter()
            .filter(|r| roots.contains(&u.termenv.rules[r.index()].root_term))
            .count(),
        e_root_rules.len(),
        excluded_roots.len(),
        introduced.len(),
    );
    o.push_str("end Isle.Opt.Closure\n");
    println!(
        "opt closure: {n} rules, {nt} terms ({n_ext} extern, {n_ext_spec} with spec), {} E root rules, \
         introduced opcodes {introduced:?}, {} root rules excluded",
        e_root_rules.len(),
        excluded_roots.len()
    );
    Ok(o)
}
