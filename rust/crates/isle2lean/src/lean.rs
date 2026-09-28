//! Lean rendering of the analysed ISLE program (datatypes in `FV/Isle/Syntax.lean`).

use crate::load::Unit;
use cranelift_isle::ast;
use cranelift_isle::lexer::Pos;
use cranelift_isle::printer::{SExpr, ToSExpr};
use cranelift_isle::sema::{
    self, BuiltinType, ConstructorKind, ExtractorKind, Fields, IntType, TermKind,
};
use std::collections::HashMap;
use std::fmt::Write;

/// Lean string literal.
pub fn lstr(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(o, "\\x{:02x}", c as u32);
            }
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

/// Map a name to `[A-Za-z0-9_]*`.
pub fn sanitize(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
        .collect()
}

/// A Lean name component for an arbitrary ISLE symbol: `«name»` (ISLE names may contain `.`,
/// and some are Lean keywords).
pub fn lname(s: &str) -> String {
    assert!(!s.contains('»') && !s.contains('«'), "ISLE name {s} cannot be quoted");
    format!("«{s}»")
}

pub fn lint(i: i128) -> String {
    if i < 0 { format!("({i})") } else { i.to_string() }
}

fn lbool(b: bool) -> &'static str {
    if b { "true" } else { "false" }
}

fn file_stem(name: &str) -> &str {
    let base = name.rsplit('/').next().unwrap_or(name);
    base.strip_suffix(".isle").unwrap_or(base)
}

/// Stable Lean names of the rules, indexed by `RuleId`:
/// `rule_<file stem>_<1-based line>`, with `_2`, `_3`, ... appended (in rule
/// order) on the rare collision of two rules starting on the same line.
pub fn rule_names(u: &Unit) -> Vec<String> {
    let mut seen: HashMap<String, usize> = HashMap::new();
    u.termenv
        .rules
        .iter()
        .map(|r| {
            let base = format!(
                "rule_{}_{}",
                sanitize(file_stem(u.file_name(r.pos.file))),
                u.line(r.pos)
            );
            let n = seen.entry(base.clone()).or_insert(0);
            *n += 1;
            if *n == 1 { base } else { format!("{base}_{n}") }
        })
        .collect()
}

/// Lean names of the type definitions, indexed by `TypeId`.
pub fn type_names(u: &Unit) -> Vec<String> {
    let mut seen: HashMap<String, usize> = HashMap::new();
    u.tyenv
        .types
        .iter()
        .map(|t| {
            let base = format!("ty_{}", sanitize(t.name(&u.tyenv)));
            let n = seen.entry(base.clone()).or_insert(0);
            *n += 1;
            if *n == 1 { base } else { format!("{base}_{n}") }
        })
        .collect()
}

pub fn pos(u: &Unit, p: Pos) -> String {
    format!("⟨{}, {}⟩", lstr(u.file_name(p.file)), u.line(p))
}

pub fn sexpr(e: &SExpr) -> String {
    let mut o = String::new();
    sexpr_into(e, &mut o);
    o
}

fn sexpr_into(e: &SExpr, o: &mut String) {
    match e {
        SExpr::Atom(a) => {
            o.push_str("(.atom ");
            o.push_str(&lstr(a));
            o.push(')');
        }
        SExpr::Binding(n, e) => {
            o.push_str("(.binding ");
            o.push_str(&lstr(n));
            o.push(' ');
            sexpr_into(e, o);
            o.push(')');
        }
        SExpr::List(es) => {
            o.push_str("(.list [");
            for (i, e) in es.iter().enumerate() {
                if i > 0 {
                    o.push_str(", ");
                }
                sexpr_into(e, o);
            }
            o.push_str("])");
        }
    }
}

fn int_ty(t: IntType) -> &'static str {
    match t {
        IntType::U8 => ".u8",
        IntType::U16 => ".u16",
        IntType::U32 => ".u32",
        IntType::U64 => ".u64",
        IntType::U128 => ".u128",
        IntType::USize => ".usize",
        IntType::I8 => ".i8",
        IntType::I16 => ".i16",
        IntType::I32 => ".i32",
        IntType::I64 => ".i64",
        IntType::I128 => ".i128",
        IntType::ISize => ".isize",
    }
}

fn fields(u: &Unit, f: &Fields) -> (String, String) {
    match f {
        Fields::Unit => (".unit".into(), "[]".into()),
        Fields::Struct(s) => (
            ".named".into(),
            format!(
                "[{}]",
                s.fields
                    .iter()
                    .map(|f| format!("⟨{}, {}⟩", lstr(u.sym(f.name)), f.ty.index()))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ),
        Fields::Tuple(t) => (
            ".tuple".into(),
            format!(
                "[{}]",
                t.fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| format!("⟨{}, {}⟩", lstr(&i.to_string()), f.ty.index()))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ),
    }
}

/// A `TypeDef` literal. Enum variants go one per line.
pub fn type_def(u: &Unit, t: &sema::Type) -> String {
    let id = t.id().index();
    let name = lstr(t.name(&u.tyenv));
    let p = match t.pos() {
        Some(p) => format!("some {}", pos(u, p)),
        None => "none".into(),
    };
    let kind = match t {
        sema::Type::Builtin(BuiltinType::Bool) => ".bool".to_string(),
        sema::Type::Builtin(BuiltinType::Int(it)) => format!("(.int {})", int_ty(*it)),
        sema::Type::Primitive(..) => ".primitive".to_string(),
        sema::Type::Enum {
            is_extern,
            variants,
            ..
        } => {
            let mut s = format!("(.enum {} [", lbool(*is_extern));
            for (i, v) in variants.iter().enumerate() {
                let (fk, fs) = fields(u, &v.fields);
                let _ = write!(
                    s,
                    "{}\n    ⟨{}, {}, {}, {}⟩",
                    if i > 0 { "," } else { "" },
                    lstr(u.sym(v.name)),
                    lstr(u.sym(v.fullname)),
                    fk,
                    fs
                );
            }
            s.push_str("])");
            s
        }
        sema::Type::Struct {
            is_extern, fields: f, ..
        } => {
            let (fk, fs) = fields(u, f);
            format!("(.struct {} {} {})", lbool(*is_extern), fk, fs)
        }
    };
    format!("⟨{id}, {name}, {kind}, {p}⟩")
}

/// The `Ids` module body (after `header`): `@[match_pattern]` constants for every type id
/// (`TyId.«T»`), every enum variant index (`VIdx.«T».«V»`) and every term id (`TId.«t»`), so
/// the backend decodes enum values and dispatches extern helpers on generated numbers (a
/// `Nat`-literal match) instead of by-name lookups into `program`.
pub fn ids_module(u: &Unit, header: &str, ns: &str) -> String {
    let mut o = String::from(header);
    o.push_str("/-! ### Type ids -/\n\n");
    for t in &u.tyenv.types {
        let _ = writeln!(
            o,
            "@[match_pattern] abbrev TyId.{} : TypeId := {}",
            lname(t.name(&u.tyenv)),
            t.id().index()
        );
    }
    o.push_str("\n/-! ### Enum variant indices -/\n\n");
    for t in &u.tyenv.types {
        if let sema::Type::Enum { variants, .. } = t {
            for (k, v) in variants.iter().enumerate() {
                let _ = writeln!(
                    o,
                    "@[match_pattern] abbrev VIdx.{}.{} : Nat := {k}",
                    lname(t.name(&u.tyenv)),
                    lname(u.sym(v.name))
                );
            }
        }
    }
    o.push_str("\n/-! ### Term ids -/\n\n");
    for t in &u.termenv.terms {
        let _ = writeln!(
            o,
            "@[match_pattern] abbrev TId.{} : TermId := {}",
            lname(u.sym(t.name)),
            t.id.index()
        );
    }
    let _ = writeln!(o, "\nend {ns}");
    o
}

/// Source forms `(extractor (T args..) template)` of internal extractors, by
/// term name. (The sema template has macro-argument holes the printer rejects.)
pub fn extractor_forms(u: &Unit) -> HashMap<String, SExpr> {
    u.defs
        .iter()
        .filter_map(|d| match d {
            ast::Def::Extractor(e) => Some((e.term.0.clone(), d.to_sexpr())),
            _ => None,
        })
        .collect()
}

pub fn term(u: &Unit, extractors: &HashMap<String, SExpr>, t: &sema::Term) -> String {
    let kind = match &t.kind {
        TermKind::EnumVariant { variant } => format!("(.enumVariant {})", variant.index()),
        TermKind::Struct => ".struct".to_string(),
        TermKind::Decl {
            flags,
            constructor_kind,
            extractor_kind,
        } => {
            let c = match constructor_kind {
                None => "none".to_string(),
                Some(ConstructorKind::InternalConstructor) => "(some .internal)".to_string(),
                Some(ConstructorKind::ExternalConstructor { name }) => {
                    format!("(some (.external {}))", lstr(u.sym(*name)))
                }
            };
            let e = match extractor_kind {
                None => "none".to_string(),
                Some(ExtractorKind::InternalExtractor { .. }) => {
                    let form = &extractors[u.sym(t.name)];
                    format!("(some (.internal {}))", sexpr(form))
                }
                Some(ExtractorKind::ExternalExtractor {
                    name, infallible, ..
                }) => format!(
                    "(some (.external {} {}))",
                    lstr(u.sym(*name)),
                    lbool(*infallible)
                ),
            };
            format!(
                "(.decl ⟨{}, {}, {}, {}⟩ {} {})",
                lbool(flags.pure),
                lbool(flags.multi),
                lbool(flags.partial),
                lbool(flags.rec),
                c,
                e
            )
        }
    };
    format!(
        "⟨{}, {}, [{}], {}, {}, {}⟩",
        t.id.index(),
        lstr(u.sym(t.name)),
        t.arg_tys
            .iter()
            .map(|a| a.index().to_string())
            .collect::<Vec<_>>()
            .join(", "),
        t.ret_ty.index(),
        kind,
        pos(u, t.decl_pos)
    )
}

pub fn pattern(u: &Unit, p: &sema::Pattern, o: &mut String) {
    use sema::Pattern as P;
    match p {
        P::BindPattern(ty, v, sub) => {
            let _ = write!(o, "(.bind {} {} ", ty.index(), v.index());
            pattern(u, sub, o);
            o.push(')');
        }
        P::Var(ty, v) => {
            let _ = write!(o, "(.var {} {})", ty.index(), v.index());
        }
        P::ConstBool(ty, b) => {
            let _ = write!(o, "(.constBool {} {})", ty.index(), lbool(*b));
        }
        P::ConstInt(ty, i) => {
            let _ = write!(o, "(.constInt {} {})", ty.index(), lint(*i));
        }
        P::ConstPrim(ty, s) => {
            let _ = write!(o, "(.constPrim {} {})", ty.index(), lstr(u.sym(*s)));
        }
        P::Term(ty, t, args) => {
            let _ = write!(o, "(.term {} {} [", ty.index(), t.index());
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    o.push_str(", ");
                }
                pattern(u, a, o);
            }
            o.push_str("])");
        }
        P::Wildcard(ty) => {
            let _ = write!(o, "(.wildcard {})", ty.index());
        }
        P::And(ty, ps) => {
            let _ = write!(o, "(.and {} [", ty.index());
            for (i, a) in ps.iter().enumerate() {
                if i > 0 {
                    o.push_str(", ");
                }
                pattern(u, a, o);
            }
            o.push_str("])");
        }
    }
}

pub fn expr(u: &Unit, e: &sema::Expr, o: &mut String) {
    use sema::Expr as E;
    match e {
        E::Term(ty, t, args) => {
            let _ = write!(o, "(.term {} {} [", ty.index(), t.index());
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    o.push_str(", ");
                }
                expr(u, a, o);
            }
            o.push_str("])");
        }
        E::Var(ty, v) => {
            let _ = write!(o, "(.var {} {})", ty.index(), v.index());
        }
        E::ConstBool(ty, b) => {
            let _ = write!(o, "(.constBool {} {})", ty.index(), lbool(*b));
        }
        E::ConstInt(ty, i) => {
            let _ = write!(o, "(.constInt {} {})", ty.index(), lint(*i));
        }
        E::ConstPrim(ty, s) => {
            let _ = write!(o, "(.constPrim {} {})", ty.index(), lstr(u.sym(*s)));
        }
        E::Let { ty, bindings, body } => {
            let _ = write!(o, "(.let {} [", ty.index());
            for (i, (v, vty, e)) in bindings.iter().enumerate() {
                if i > 0 {
                    o.push_str(", ");
                }
                let _ = write!(o, "({}, {}, ", v.index(), vty.index());
                expr(u, e, o);
                o.push(')');
            }
            o.push_str("] ");
            expr(u, body, o);
            o.push(')');
        }
    }
}

/// Positions of rules that carry an explicit name in the source (`(rule name ...)`); sema
/// also names a term's only rule after the term.
pub fn explicitly_named_rules(u: &Unit) -> std::collections::HashSet<Pos> {
    u.defs
        .iter()
        .filter_map(|d| match d {
            ast::Def::Rule(r) if r.name.is_some() => Some(r.pos),
            _ => None,
        })
        .collect()
}

/// A `def <name> : Rule` block.
pub fn rule_def(u: &Unit, r: &sema::Rule, name: &str, explicit_name: bool) -> String {
    let term = &u.termenv.terms[r.root_term.index()];
    let mut o = String::new();
    let _ = writeln!(
        o,
        "/-- `{}:{}`, term `{}`, priority {} -/",
        u.file_name(r.pos.file),
        u.line(r.pos),
        u.sym(term.name),
        r.prio
    );
    let _ = writeln!(o, "def {name} : Rule where");
    let _ = writeln!(o, "  id := {}", r.id.index());
    let _ = writeln!(o, "  name := {}", lstr(name));
    let _ = writeln!(
        o,
        "  isleName := {}",
        match r.name {
            Some(s) => format!("some {}", lstr(u.sym(s))),
            None => "none".into(),
        }
    );
    let _ = writeln!(o, "  explicitName := {}", lbool(explicit_name));
    let _ = writeln!(o, "  term := {}", r.root_term.index());
    o.push_str("  args := [");
    for (i, a) in r.args.iter().enumerate() {
        if i > 0 {
            o.push_str(", ");
        }
        pattern(u, a, &mut o);
    }
    o.push_str("]\n");
    o.push_str("  iflets := [");
    for (i, il) in r.iflets.iter().enumerate() {
        if i > 0 {
            o.push_str(",\n    ");
        }
        o.push('⟨');
        pattern(u, &il.lhs, &mut o);
        o.push_str(", ");
        expr(u, &il.rhs, &mut o);
        o.push('⟩');
    }
    o.push_str("]\n");
    o.push_str("  rhs := ");
    expr(u, &r.rhs, &mut o);
    o.push('\n');
    let _ = writeln!(
        o,
        "  vars := [{}]",
        r.vars
            .iter()
            .map(|v| format!("({}, {})", lstr(u.sym(v.name)), v.ty.index()))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let _ = writeln!(o, "  prio := {}", lint(r.prio as i128));
    let _ = writeln!(o, "  pos := {}", pos(u, r.pos));
    o
}

/// One exported spec-language definition.
pub struct SpecItem {
    pub kind: &'static str,
    pub name: String,
    pub term: Option<usize>,
    pub rule: Option<usize>,
    pub pos: Pos,
    pub body: SExpr,
}

pub fn spec_items(u: &Unit) -> Vec<SpecItem> {
    let term_of = |id: &ast::Ident| {
        u.termenv
            .get_term_by_name(&u.tyenv, id)
            .map(|t| t.index())
    };
    let mut out = Vec::new();
    for d in &u.defs {
        let item = match d {
            ast::Def::Spec(s) => SpecItem {
                kind: ".spec",
                name: s.term.0.clone(),
                term: term_of(&s.term),
                rule: None,
                pos: s.pos,
                body: d.to_sexpr(),
            },
            ast::Def::SpecMacro(m) => SpecItem {
                kind: ".specMacro",
                name: m.name.0.clone(),
                term: None,
                rule: None,
                pos: m.pos,
                body: d.to_sexpr(),
            },
            ast::Def::Model(m) => SpecItem {
                kind: ".model",
                name: m.name.0.clone(),
                term: None,
                rule: None,
                pos: m.name.1,
                body: d.to_sexpr(),
            },
            ast::Def::State(s) => SpecItem {
                kind: ".state",
                name: s.name.0.clone(),
                term: None,
                rule: None,
                pos: s.pos,
                body: d.to_sexpr(),
            },
            ast::Def::Form(f) => SpecItem {
                kind: ".form",
                name: f.name.0.clone(),
                term: None,
                rule: None,
                pos: f.pos,
                body: d.to_sexpr(),
            },
            ast::Def::Instantiation(i) => SpecItem {
                kind: ".instantiate",
                name: i.term.0.clone(),
                term: term_of(&i.term),
                rule: None,
                pos: i.pos,
                body: d.to_sexpr(),
            },
            ast::Def::Attr(a) => {
                let (name, term, rule) = match &a.target {
                    ast::AttrTarget::Term(t) => (t.0.clone(), term_of(t), None),
                    ast::AttrTarget::Rule(r) => (
                        r.0.clone(),
                        None,
                        u.termenv.get_rule_by_name(&u.tyenv, r).map(|r| r.index()),
                    ),
                };
                SpecItem {
                    kind: ".attr",
                    name,
                    term,
                    rule,
                    pos: a.pos,
                    body: d.to_sexpr(),
                }
            }
            _ => continue,
        };
        out.push(item);
    }
    out
}

fn opt(o: Option<usize>) -> String {
    match o {
        Some(i) => format!("(some {i})"),
        None => "none".into(),
    }
}

pub fn spec_item(u: &Unit, s: &SpecItem) -> String {
    format!(
        "⟨{}, {}, {}, {}, {}, {}⟩",
        s.kind,
        lstr(&s.name),
        opt(s.term),
        opt(s.rule),
        pos(u, s.pos),
        sexpr(&s.body)
    )
}
