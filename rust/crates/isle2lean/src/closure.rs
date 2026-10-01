//! Rules reachable from `lower`/`lower_branch` for the emitter opcode subset E
//! (`docs/contracts/clif-subset.md`, `clif-subset-v2`) at `i8`..`i64`.
//!
//! Root selection (sound for E programs, whose values all have types
//! `i8 i16 i32 i64` and whose instructions all have E opcodes): a root rule
//! is dropped iff its main LHS pattern (the `args`, not the if-lets)
//!
//! - mentions an `Opcode.X` variant with `X` not in E, or
//! - mentions a `Type` constant other than `$I8 $I16 $I32 $I64`, or
//! - uses one of the `NON_SCALAR_INT` extern extractors, each of which fails on
//!   every scalar integer type of width <= 64 (checked against
//!   `cranelift/codegen/src/isle_prelude.rs`).
//!
//! ISLE patterns are conjunctions, so each of these is a necessary condition
//! for the rule to match. Then every rule of every internal-constructor term
//! mentioned (LHS, if-let or RHS) by a rule in the closure is added,
//! transitively, without filtering (types passed to internal terms can be
//! computed, so filtering there would be unsound). The same syntactic test is
//! reported for those rules as `lhsReasons` (a hint, not a proof).

use crate::lean::lstr;
use crate::load::Unit;
use anyhow::{Result, anyhow};
use cranelift_isle::ast;
use cranelift_isle::sema::{self, RuleId, TermId, TermKind};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write;

/// E opcodes (CLIF names), `clif-subset-v2`.
pub const E_OPCODES: &[&str] = &[
    "iconst", "iadd", "isub", "ineg", "imul", "umulhi", "smulhi", "udiv", "urem", "sdiv", "srem",
    "band", "bor", "bxor", "bnot", "ishl", "ushr", "sshr", "rotl", "rotr", "clz", "ctz", "popcnt",
    "icmp", "uextend", "sextend", "ireduce", "load", "store", "uload8", "uload16", "uload32",
    "sload8", "sload16", "sload32", "istore8", "istore16", "istore32", "stack_addr", "jump",
    "brif", "br_table", "return", "call", "trap",
    // clif-subset-v2 (docs/research/rust-clif-survey.md):
    "nop", "symbol_value", "select", "smin", "smax", "umin", "umax", "bswap", "bitrev",
    // rust-route step 4: indirect calls and function addresses compile but are flagged
    // unverified (outside ); their lowering rules must not be flagged outside
    // the closure (the survey's  functions use them).
    "call_indirect", "func_addr",
];

/// Opcodes of the backend closure only (not of the mid-end closure, `opt_closure`, whose
/// subset stays `E_OPCODES`): `bmask`, the atomics and `fence` (agent/atomics-proof: inside
/// `E2E.backend_correct_final`; Cranelift's non-LSE rules, `load_acquire`/`store_release` =
/// ldar/stlr and the `atomic_rmw_loop`/`atomic_cas_loop` LL/SC pseudo-instructions), and
/// `tls_value` (agent/stack-tls-proof: the `elf_gd` TLSDESC sequence; the `macho` rule is a
/// root too and is proven never to match, `tls_model` is `elf_gd`).
pub const BACKEND_EXTRA_OPCODES: &[&str] =
    &["bmask", "atomic_load", "atomic_store", "atomic_rmw", "atomic_cas", "fence", "tls_value"];

/// Extern extractors on ISA flags the backend disables (`isa_flags`: no LSE), which fail on
/// every instruction (the Lean checker's `flagOff`).
pub const FLAG_OFF: &[&str] = &["use_lse"];

pub const ROOTS: &[&str] = &["lower", "lower_branch"];

/// Names of `Type` constants (the lexer drops the `$`) E values can have.
pub const TYPE_CONSTS_OK: &[&str] = &["I8", "I16", "I32", "I64"];

/// Extern extractors on `Type` that fail for `i8 i16 i32 i64`.
pub const NON_SCALAR_INT: &[&str] = &[
    "ty_128",
    "ty_scalar_float",
    "ty_float_or_vec",
    "ty_vector_float",
    "ty_vector_not_float",
    "ty_vec64",
    "ty_vec128",
    "ty_dyn_vec64",
    "ty_dyn_vec128",
    "ty_vec64_int",
    "ty_vec128_int",
    "multi_lane",
    "dynamic_lane",
    "ty_dyn64_int",
    "ty_dyn128_int",
    "lane_fits_in_32",
];

/// `veri --default-excludes` tags (`cranelift/isle/veri/veri/src/bin/veri.rs`).
pub const DEFAULT_EXCLUDES: &[&str] = &[
    "vector",
    "atomics",
    "spectre",
    "narrowfloat",
    "amode_const",
    "i128",
    "wasm_category_stack",
    "slow",
];

pub fn camel(op: &str) -> String {
    op.split('_')
        .map(|w| {
            let mut c = w.chars();
            match c.next() {
                Some(f) => f.to_ascii_uppercase().to_string() + c.as_str(),
                None => String::new(),
            }
        })
        .collect()
}

/// A term or a primitive constant occurring in a pattern.
pub enum Atom {
    Term(TermId),
    Const(sema::TypeId, sema::Sym),
}

pub fn pat_terms(p: &sema::Pattern, out: &mut Vec<Atom>) {
    use sema::Pattern as P;
    match p {
        P::BindPattern(_, _, s) => pat_terms(s, out),
        P::Term(_, t, args) => {
            out.push(Atom::Term(*t));
            for a in args {
                pat_terms(a, out);
            }
        }
        P::And(_, ps) => {
            for a in ps {
                pat_terms(a, out);
            }
        }
        P::ConstPrim(ty, s) => out.push(Atom::Const(*ty, *s)),
        P::Var(..) | P::ConstBool(..) | P::ConstInt(..) | P::Wildcard(..) => {}
    }
}

pub fn expr_terms(e: &sema::Expr, out: &mut BTreeSet<TermId>) {
    use sema::Expr as E;
    match e {
        E::Term(_, t, args) => {
            out.insert(*t);
            for a in args {
                expr_terms(a, out);
            }
        }
        E::Let { bindings, body, .. } => {
            for (_, _, b) in bindings {
                expr_terms(b, out);
            }
            expr_terms(body, out);
        }
        E::Var(..) | E::ConstBool(..) | E::ConstInt(..) | E::ConstPrim(..) => {}
    }
}

/// All terms a rule mentions (LHS, if-lets, RHS).
pub fn rule_terms(r: &sema::Rule) -> BTreeSet<TermId> {
    let mut v = Vec::new();
    for a in &r.args {
        pat_terms(a, &mut v);
    }
    for il in &r.iflets {
        pat_terms(&il.lhs, &mut v);
    }
    let mut s: BTreeSet<TermId> = v
        .into_iter()
        .filter_map(|a| match a {
            Atom::Term(t) => Some(t),
            Atom::Const(..) => None,
        })
        .collect();
    for il in &r.iflets {
        expr_terms(&il.rhs, &mut s);
    }
    expr_terms(&r.rhs, &mut s);
    s
}

/// Why the main LHS of `r` cannot match in an E program (empty: may match).
fn lhs_reasons(u: &Unit, r: &sema::Rule, e_ops: &HashSet<String>) -> Vec<String> {
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
                    if !e_ops.contains(op) {
                        reasons.insert(name.to_string());
                    }
                }
            }
            TermKind::Decl { .. } => {
                if term.has_external_extractor()
                    && (NON_SCALAR_INT.contains(&name) || FLAG_OFF.contains(&name))
                {
                    reasons.insert(name.to_string());
                }
            }
            TermKind::Struct => {}
        }
    }
    reasons.into_iter().collect()
}

pub struct Attrs {
    pub term_tags: HashMap<usize, BTreeSet<String>>,
    pub rule_tags: HashMap<usize, BTreeSet<String>>,
    pub chain: HashSet<usize>,
    pub spec: HashSet<usize>,
}

pub fn attrs(u: &Unit) -> Attrs {
    let mut a = Attrs {
        term_tags: HashMap::new(),
        rule_tags: HashMap::new(),
        chain: HashSet::new(),
        spec: HashSet::new(),
    };
    for d in &u.defs {
        match d {
            ast::Def::Spec(s) => {
                if let Some(t) = u.termenv.get_term_by_name(&u.tyenv, &s.term) {
                    a.spec.insert(t.index());
                }
            }
            ast::Def::Attr(at) => {
                let (tags, id) = match &at.target {
                    ast::AttrTarget::Term(t) => match u.termenv.get_term_by_name(&u.tyenv, t) {
                        Some(t) => (&mut a.term_tags, t.index()),
                        None => continue,
                    },
                    ast::AttrTarget::Rule(r) => match u.termenv.get_rule_by_name(&u.tyenv, r) {
                        Some(r) => (&mut a.rule_tags, r.index()),
                        None => continue,
                    },
                };
                for k in &at.kinds {
                    match k {
                        ast::AttrKind::Tag(t) => {
                            tags.entry(id).or_default().insert(t.0.clone());
                        }
                        ast::AttrKind::Chain => {
                            if let ast::AttrTarget::Term(_) = at.target {
                                a.chain.insert(id);
                            }
                        }
                        ast::AttrKind::Priority => {}
                    }
                }
            }
            _ => {}
        }
    }
    a
}

pub fn lstrs<'a>(it: impl IntoIterator<Item = &'a String>) -> String {
    format!(
        "[{}]",
        it.into_iter().map(|s| lstr(s)).collect::<Vec<_>>().join(", ")
    )
}

pub fn lopt(s: Option<&str>) -> String {
    match s {
        Some(s) => format!("(some {})", lstr(s)),
        None => "none".into(),
    }
}

pub fn render(u: &Unit, rule_names: &[String]) -> Result<String> {
    let e_ops: HashSet<String> =
        E_OPCODES.iter().chain(BACKEND_EXTRA_OPCODES).map(|o| camel(o)).collect();
    // Every E opcode must exist as an `Opcode` variant.
    for op in &e_ops {
        let id = ast::Ident(format!("Opcode.{op}"), Default::default());
        u.termenv
            .get_term_by_name(&u.tyenv, &id)
            .ok_or_else(|| anyhow!("E opcode Opcode.{op} not found"))?;
    }
    let attrs = attrs(u);
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

    let mut in_closure: BTreeSet<RuleId> = BTreeSet::new();
    let mut excluded_roots: Vec<(RuleId, Vec<String>)> = Vec::new();
    let mut work: Vec<RuleId> = Vec::new();
    for t in &roots {
        for &r in rules_of.get(t).map(|v| v.as_slice()).unwrap_or(&[]) {
            let reasons = lhs_reasons(u, &u.termenv.rules[r.index()], &e_ops);
            if reasons.is_empty() {
                if in_closure.insert(r) {
                    work.push(r);
                }
            } else {
                excluded_roots.push((r, reasons));
            }
        }
    }
    let mut terms: BTreeSet<TermId> = roots.iter().copied().collect();
    let mut expanded: HashSet<TermId> = roots.iter().copied().collect();
    while let Some(r) = work.pop() {
        for t in rule_terms(&u.termenv.rules[r.index()]) {
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

    let mut o = String::new();
    o.push_str(
        "-- Generated by `rust/crates/isle2lean` from the Cranelift 0.136.1 aarch64 ISLE unit.\n\
         -- Do not edit. Regenerate: `cargo run --manifest-path rust/Cargo.toml -p isle2lean --release`.\n\
         import FV.Isle.Syntax\n\nnamespace Isle.Aarch64.Closure\nopen Isle\n\n",
    );
    o.push_str(
        "/-! Rules and terms reachable from `lower`/`lower_branch` for the emitter subset E\n\
         (`clif-subset-v2`) at `i8`..`i64`; see `docs/contracts/isle.md` (\"Closure\") for the\n\
         selection method and what `lhsReasons` / `defaultExcludedBy` mean. -/\n\n",
    );
    let mut ops: Vec<String> =
        E_OPCODES.iter().chain(BACKEND_EXTRA_OPCODES).map(|s| s.to_string()).collect();
    ops.sort();
    let _ = writeln!(o, "def opcodes : List String := {}\n", lstrs(&ops));
    let roots_s: Vec<String> = ROOTS.iter().map(|s| s.to_string()).collect();
    let _ = writeln!(o, "def roots : List String := {}\n", lstrs(&roots_s));
    let de: Vec<String> = DEFAULT_EXCLUDES.iter().map(|s| s.to_string()).collect();
    let _ = writeln!(o, "def defaultExcludes : List String := {}\n", lstrs(&de));
    let nsi: Vec<String> = NON_SCALAR_INT.iter().map(|s| s.to_string()).collect();
    let _ = writeln!(o, "def nonScalarIntExtractors : List String := {}\n", lstrs(&nsi));

    // Rules.
    let mut n_excl = 0;
    let mut n_hint = 0;
    o.push_str(
        "/-- Closure rules: `⟨rule id, name, term id, isRoot, tags, defaultExcludedBy, lhsReasons⟩`. -/\n\
         def rules : Array ClosureRule := #[\n",
    );
    let n = in_closure.len();
    for (i, r) in in_closure.iter().enumerate() {
        let rule = &u.termenv.rules[r.index()];
        let mut tags: BTreeSet<String> =
            attrs.rule_tags.get(&r.index()).cloned().unwrap_or_default();
        tags.extend(tags_of_term(rule.root_term.index()));
        for t in rule_terms(rule) {
            tags.extend(tags_of_term(t.index()));
        }
        let excl: Vec<String> = tags
            .iter()
            .filter(|t| DEFAULT_EXCLUDES.contains(&t.as_str()))
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

    // Excluded root rules.
    o.push_str(
        "\n/-- Root rules left out, with the LHS facts that rule them out for E programs. -/\n\
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

    // Terms.
    let mut n_ext_ctor = 0;
    let mut n_ext_ext = 0;
    let mut n_ext_spec = 0;
    let mut n_ext = 0;
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

    let _ = writeln!(
        o,
        "\n/-- Summary counts (also in `docs/contracts/isle.md`). -/\n\
         def summary : List (String × Nat) := [\n  \
         (\"rules\", {n}), (\"rootRules\", {}), (\"excludedRootRules\", {}),\n  \
         (\"rulesExcludedByDefaultTags\", {n_excl}), (\"rulesWithLhsReasons\", {n_hint}),\n  \
         (\"terms\", {nt}), (\"externTerms\", {n_ext}), (\"externConstructors\", {n_ext_ctor}),\n  \
         (\"externExtractors\", {n_ext_ext}), (\"externTermsWithSpec\", {n_ext_spec})]\n",
        in_closure
            .iter()
            .filter(|r| roots.contains(&u.termenv.rules[r.index()].root_term))
            .count(),
        excluded_roots.len(),
    );
    o.push_str("end Isle.Aarch64.Closure\n");
    println!(
        "closure: {n} rules, {nt} terms ({n_ext} extern, {n_ext_spec} with spec), {} root rules excluded",
        excluded_roots.len()
    );
    Ok(o)
}
