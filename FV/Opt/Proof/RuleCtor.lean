import FV.Isle.Opt.Simplify
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

@[opt_monad] theorem ctorFn_value_array_2_ctor (a : V) (b : V) (st : St σ) :
    ctorFn G "value_array_2_ctor" [a, b] st =
      ((do
        pure (some (.values [a, b]))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_value_array_3_ctor (a : V) (b : V) (c : V) (st : St σ) :
    ctorFn G "value_array_3_ctor" [a, b, c] st =
      ((do
        pure (some (.values [a, b, c]))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_bswap16 (n : Int) (st : St σ) :
    ctorFn G "u64_bswap16" [.int n] st =
      ((do
        pure (some (V.int (Rust.bswap 2 n)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_bswap32 (n : Int) (st : St σ) :
    ctorFn G "u64_bswap32" [.int n] st =
      ((do
        pure (some (V.int (Rust.bswap 4 n)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_bswap64 (n : Int) (st : St σ) :
    ctorFn G "u64_bswap64" [.int n] st =
      ((do
        pure (some (V.int (Rust.bswap 8 n)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_div_const_magic_u32 (d : Int) (st : St σ) :
    ctorFn G "div_const_magic_u32" [.int d] st =
      ((do
        let (m, a, s) := Rust.magicU 32 d.toNat
        pure (some (dcm TyId.«DivConstMagicU32» [.int m, .bool a, .int (Rust.asU32 s)]))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_div_const_magic_u64 (d : Int) (st : St σ) :
    ctorFn G "div_const_magic_u64" [.int d] st =
      ((do
        let (m, a, s) := Rust.magicU 64 d.toNat
        pure (some (dcm TyId.«DivConstMagicU64» [.int m, .bool a, .int (Rust.asU32 s)]))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_div_const_magic_s32 (d : Int) (st : St σ) :
    ctorFn G "div_const_magic_s32" [.int d] st =
      ((do
        let (m, s) := Rust.magicS 32 d
        pure (some (dcm TyId.«DivConstMagicS32» [.int m, .int (Rust.asU32 s)]))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_div_const_magic_s64 (d : Int) (st : St σ) :
    ctorFn G "div_const_magic_s64" [.int d] st =
      ((do
        let (m, s) := Rust.magicS 64 d
        pure (some (dcm TyId.«DivConstMagicS64» [.int m, .int (Rust.asU32 s)]))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_sdiv (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_sdiv" [.ty t, .int x, .int y] st =
      ((do
        pure (Option.map V.int (← panics (Rust.imm64Sdiv t x y)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_udiv (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_udiv" [.ty t, .int x, .int y] st =
      ((do
        pure (Option.map V.int (← panics (Rust.imm64Udiv t x y)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_srem (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_srem" [.ty t, .int x, .int y] st =
      ((do
        pure (Option.map V.int (← panics (Rust.imm64Srem t x y)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_urem (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_urem" [.ty t, .int x, .int y] st =
      ((do
        pure (Option.map V.int (← panics (Rust.imm64Urem t x y)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_add (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_add" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Add t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_sub (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_sub" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Sub t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_mul (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_mul" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Mul t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_and (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_and" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64And t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_or (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_or" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Or t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_xor (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_xor" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Xor t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_not (t : CTy) (x : Int) (st : St σ) :
    ctorFn G "imm64_not" [.ty t, .int x] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Not t x))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_neg (t : CTy) (x : Int) (st : St σ) :
    ctorFn G "imm64_neg" [.ty t, .int x] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Neg t x))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_umin (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_umin" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Umin t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_umax (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_umax" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Umax t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_smin (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_smin" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Smin t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_smax (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_smax" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Smax t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_shl (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_shl" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Shl t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_ushr (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_ushr" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Ushr t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_sshr (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_sshr" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Sshr t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_rotl (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_rotl" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Rotl t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_rotr (t : CTy) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_rotr" [.ty t, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Rotr t x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_clz (t : CTy) (x : Int) (st : St σ) :
    ctorFn G "imm64_clz" [.ty t, .int x] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Clz t x))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_ctz (t : CTy) (x : Int) (st : St σ) :
    ctorFn G "imm64_ctz" [.ty t, .int x] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Ctz t x))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_icmp (t : CTy) (c : V) (x : Int) (y : Int) (st : St σ) :
    ctorFn G "imm64_icmp" [.ty t, c, .int x, .int y] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Icmp t (← c.cc?) x y))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i64_sextend_u64 (t : CTy) (x : Int) (st : St σ) :
    ctorFn G "i64_sextend_u64" [.ty t, .int x] st =
      ((do
        pure (some (V.int (← panics (Rust.i64SextendU64 t x))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64 (x : Int) (st : St σ) :
    ctorFn G "imm64" [.int x] st =
      ((do
        pure (some (V.int (Rust.asI64 x)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_imm64_masked (t : CTy) (x : Int) (st : St σ) :
    ctorFn G "imm64_masked" [.ty t, .int x] st =
      ((do
        pure (some (V.int (← panics (Rust.imm64Masked t x))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_ty_umax (t : CTy) (st : St σ) :
    ctorFn G "ty_umax" [.ty t] st =
      ((do
        pure (some (V.int (← panics (Rust.tyUmax t))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_ty_mask (t : CTy) (st : St σ) :
    ctorFn G "ty_mask" [.ty t] st =
      ((do
        pure (some (V.int (← panics (Rust.tyMask t))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_ty_smin (t : CTy) (st : St σ) :
    ctorFn G "ty_smin" [.ty t] st =
      ((do
        pure (some (V.int (← panics (Rust.tySmin t))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_ty_smax (t : CTy) (st : St σ) :
    ctorFn G "ty_smax" [.ty t] st =
      ((do
        pure (some (V.int (← panics (Rust.tySmax t))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_ty_bits (t : CTy) (st : St σ) :
    ctorFn G "ty_bits" [.ty t] st =
      ((do
        pure (some (V.int (← panics (Rust.tyBits t))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_ty_bits_u64 (t : CTy) (st : St σ) :
    ctorFn G "ty_bits_u64" [.ty t] st =
      ((do
        pure (some (V.int t.bits))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_lane_type (t : CTy) (st : St σ) :
    ctorFn G "lane_type" [.ty t] st =
      ((do
        pure (some (.ty t.laneType))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_ty_half_width (t : CTy) (st : St σ) :
    ctorFn G "ty_half_width" [.ty t] st =
      ((do
        pure (t.halfWidth?.map .ty)
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_ty_equal (a : CTy) (b : CTy) (st : St σ) :
    ctorFn G "ty_equal" [.ty a, .ty b] st =
      ((do
        pure (some (V.bool (a == b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_intcc_swap_args (c : V) (st : St σ) :
    ctorFn G "intcc_swap_args" [c] st =
      ((do
        pure (some (cc (Rust.intccSwapArgs (← c.cc?))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_intcc_complement (c : V) (st : St σ) :
    ctorFn G "intcc_complement" [c] st =
      ((do
        pure (some (cc (Rust.intccComplement (← c.cc?))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_signed_cond_code (c : V) (st : St σ) :
    ctorFn G "signed_cond_code" [c] st =
      ((do
        pure ((Rust.signedCondCode (← c.cc?)).map cc)
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_uextend_imm64 (t : CTy) (x : Int) (st : St σ) :
    ctorFn G "u64_uextend_imm64" [.ty t, .int x] st =
      ((do
        pure (some (V.int (← panics (Rust.u64UextendImm64 t x))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_checked_add_with_type (t : CTy) (a : Int) (b : Int) (st : St σ) :
    ctorFn G "checked_add_with_type" [.ty t, .int a, .int b] st =
      ((do
        pure (Option.map V.int (← panics (Rust.checkedAddWithType t a b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_ty_vector_not_float (t : CTy) (st : St σ) :
    ctorFn G "ty_vector_not_float" [.ty t] st =
      ((do
        pure ((Rust.tyVectorNotFloat t).map .ty)
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_pack_value_array_2 (a : V) (b : V) (st : St σ) :
    ctorFn G "pack_value_array_2" [a, b] st =
      ((do
        pure (some (.values [a, b]))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_pack_block_array_2 (a : V) (b : V) (st : St σ) :
    ctorFn G "pack_block_array_2" [a, b] st =
      ((do
        pure (some (.values [a, b]))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_make_skeleton_inst_ctor (d : V) (st : St σ) :
    ctorFn G "make_skeleton_inst_ctor" [d] st =
      ((do
        pure (some (.inst (toSkel d)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_resolve_jump_table_entry (d : Clif.BlockCall) (tbl : List Clif.BlockCall) (i : Int) (st : St σ) :
    ctorFn G "resolve_jump_table_entry" [.jumpTable d tbl, .int i] st =
      ((do
        pure (some (.blockCall (if i ≥ 0 then (tbl[i.toNat]?).getD d else d)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_block_call_block (b : Clif.BlockCall) (st : St σ) :
    ctorFn G "block_call_block" [.blockCall b] st =
      ((do
        pure (some (V.int b.block))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_just_trap_block (b : Int) (st : St σ) :
    ctorFn G "just_trap_block" [.int b] st =
      ((do
        pure ((G.trapBlock st.inner b.toNat).map .trapCode)
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_pack_value_array_3 (a : V) (b : V) (c : V) (st : St σ) :
    ctorFn G "pack_value_array_3" [a, b, c] st =
      ((do
        pure (some (.values [a, b, c]))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i32_lt (a : Int) (b : Int) (st : St σ) :
    ctorFn G "i32_lt" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a < b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i32_gt (a : Int) (b : Int) (st : St σ) :
    ctorFn G "i32_gt" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a > b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u32_lt (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u32_lt" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a < b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u32_sub (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u32_sub" [.int a, .int b] st =
      ((do
        pure (some (V.int (← panics (Rust.checkedSubU "u32_sub" a b))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u32_is_power_of_two (a : Int) (st : St σ) :
    ctorFn G "u32_is_power_of_two" [.int a] st =
      ((do
        pure (some (V.bool (Rust.isPow2 a)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i64_eq (a : Int) (b : Int) (st : St σ) :
    ctorFn G "i64_eq" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a == b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i64_ne (a : Int) (b : Int) (st : St σ) :
    ctorFn G "i64_ne" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a != b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i64_lt (a : Int) (b : Int) (st : St σ) :
    ctorFn G "i64_lt" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a < b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i64_gt (a : Int) (b : Int) (st : St σ) :
    ctorFn G "i64_gt" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a > b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i64_gt_eq (a : Int) (b : Int) (st : St σ) :
    ctorFn G "i64_gt_eq" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a ≥ b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i64_shl (a : Int) (b : Int) (st : St σ) :
    ctorFn G "i64_shl" [.int a, .int b] st =
      ((do
        pure (some (V.int (← panics (Rust.i64Shl a b))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i64_trailing_zeros (a : Int) (st : St σ) :
    ctorFn G "i64_trailing_zeros" [.int a] st =
      ((do
        pure (some (V.int (Rust.ctz64 a)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i64_wrapping_neg (a : Int) (st : St σ) :
    ctorFn G "i64_wrapping_neg" [.int a] st =
      ((do
        pure (some (V.int (Rust.asI64 (-a))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i64_cast_unsigned (a : Int) (st : St σ) :
    ctorFn G "i64_cast_unsigned" [.int a] st =
      ((do
        pure (some (V.int (Rust.asU64 a)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_eq (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_eq" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a == b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_lt (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_lt" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a < b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_lt_eq (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_lt_eq" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a ≤ b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_gt (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_gt" [.int a, .int b] st =
      ((do
        pure (some (V.bool (a > b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_wrapping_add (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_wrapping_add" [.int a, .int b] st =
      ((do
        pure (some (V.int (Rust.asU64 (a + b))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_wrapping_sub (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_wrapping_sub" [.int a, .int b] st =
      ((do
        pure (some (V.int (Rust.asU64 (a - b))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_sub (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_sub" [.int a, .int b] st =
      ((do
        pure (some (V.int (← panics (Rust.checkedSubU "u64_sub" a b))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_div (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_div" [.int a, .int b] st =
      ((do
        if b == 0 then throw s!"panic: u64_div: div failure: {a} / 0"
        pure (some (V.int (a / b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_rem (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_rem" [.int a, .int b] st =
      ((do
        if b == 0 then throw s!"panic: u64_rem: rem failure: {a} % 0"
        pure (some (V.int (a % b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_checked_rem (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_checked_rem" [.int a, .int b] st =
      ((do
        pure (Option.map V.int (if b == 0 then none else some (a % b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_and (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_and" [.int a, .int b] st =
      ((do
        pure (some (V.int (Rust.band64 a b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_or (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_or" [.int a, .int b] st =
      ((do
        pure (some (V.int (Rust.bor64 a b)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_not (a : Int) (st : St σ) :
    ctorFn G "u64_not" [.int a] st =
      ((do
        pure (some (V.int (Rust.asU64 (-a - 1))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_shl (a : Int) (b : Int) (st : St σ) :
    ctorFn G "u64_shl" [.int a, .int b] st =
      ((do
        pure (some (V.int (← panics (Rust.u64Shl a b))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_ilog2 (a : Int) (st : St σ) :
    ctorFn G "u64_ilog2" [.int a] st =
      ((do
        pure (some (V.int (← panics (Rust.u64Ilog2 a))))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_trailing_zeros (a : Int) (st : St σ) :
    ctorFn G "u64_trailing_zeros" [.int a] st =
      ((do
        pure (some (V.int (Rust.ctz64 a)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u64_is_power_of_two (a : Int) (st : St σ) :
    ctorFn G "u64_is_power_of_two" [.int a] st =
      ((do
        pure (some (V.bool (Rust.isPow2 a)))
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u16_into_u64 (a : V) (st : St σ) :
    ctorFn G "u16_into_u64" [a] st =
      ((do
        pure (some a)
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u8_into_u32 (a : V) (st : St σ) :
    ctorFn G "u8_into_u32" [a] st =
      ((do
        pure (some a)
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u8_into_u64 (a : V) (st : St σ) :
    ctorFn G "u8_into_u64" [a] st =
      ((do
        pure (some a)
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_i32_into_i64 (a : V) (st : St σ) :
    ctorFn G "i32_into_i64" [a] st =
      ((do
        pure (some a)
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u32_into_i64 (a : V) (st : St σ) :
    ctorFn G "u32_into_i64" [a] st =
      ((do
        pure (some a)
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

@[opt_monad] theorem ctorFn_u32_into_u64 (a : V) (st : St σ) :
    ctorFn G "u32_into_u64" [a] st =
      ((do
        pure (some a)
      : R (Option V)) >>= fun o => pure (o.map (·, st))) := rfl

end

end Opt.Proof
