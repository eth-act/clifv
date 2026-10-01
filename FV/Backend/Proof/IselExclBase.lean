import FV.Backend.Proof.IselFamily

/-!
# Excluded root rules: an abstract pattern checker

The root rules of `lower` outside the closure (`closureRoot r = false`) never match an
instruction of a `CtxInv` context (`ExcludedUnmatchable`). Every such rule names, in its main
pattern, a non-E opcode, a type constant other than `$I8..$I64`, or a vector/float type test
(`isle.md`, "Closure"), possibly under look-through extractors (`def_inst`, `value_type`,
`value_array_2`) or behind a disabled ISA-flag extractor (`use_lse`, …).

`fails p a q` is an over-approximating check that pattern `q` cannot match any value of the
abstract value `a` (`AV`): the instruction of a context, the `InstructionData` of an E
instruction, a CLIF value, a type among a finite list, a concrete value. It is evaluated by the
kernel over the rule list (`IselExcl.lean`); `fails_sound` (`IselExclSound.lean`) proves it
sound for every context with `CtxInv`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- Abstract values (their meaning: `AV.Holds`). -/
inductive AV where
  /-- `.inst j` for an instruction `j` of the context with CLIF instruction `c`, data
  `instData f c` and result types in `eCTys`. -/
  | inst
  /-- The `InstructionData` of an E instruction (`instData f c = .ok v`). -/
  | data
  /-- A CLIF value `.value x`. -/
  | value
  /-- `.values xs` with `n` values. -/
  | values (n : Nat)
  /-- `.ty t` with `t ∈ ts`. -/
  | tys (ts : List CTy)
  /-- Exactly this value. -/
  | exact (v : V)
  /-- Anything. -/
  | any

/-- The values an abstract value describes, in the context `ctx` of `f`. -/
def AV.Holds (f : Clif.Function) (ctx : Ctx) : AV → V → Prop
  | .inst, v => ∃ j info c, v = .inst j ∧ ctx.insts[j]? = some info ∧ info.clif = some c ∧
      instData f c = .ok info.data
  | .data, v => ∃ c, Compile.instE c = true ∧ instData f c = .ok v
  | .value, v => ∃ x, v = .value x
  | .values n, v => ∃ xs, v = .values xs ∧ xs.length = n
  | .tys ts, v => ∃ t ∈ ts, v = .ty t
  | .exact w, v => v = w
  | .any, _ => True

/-- `AV.Holds` position by position (lists of the same length). -/
def AV.HoldsAll (f : Clif.Function) (ctx : Ctx) : List AV → List V → Prop
  | [], [] => True
  | a :: as, v :: vs => a.Holds f ctx v ∧ AV.HoldsAll f ctx as vs
  | _, _ => False

/-- The variant indices of the opcodes `instData` produces (the E opcodes). -/
def eOps : List Nat :=
  [VIdx.Opcode.Iconst, VIdx.Opcode.Ineg, VIdx.Opcode.Bnot, VIdx.Opcode.Clz, VIdx.Opcode.Ctz,
   VIdx.Opcode.Popcnt, VIdx.Opcode.Bswap, VIdx.Opcode.Bitrev,
   VIdx.Opcode.Iadd, VIdx.Opcode.Isub, VIdx.Opcode.Imul, VIdx.Opcode.Umulhi, VIdx.Opcode.Smulhi,
   VIdx.Opcode.Band, VIdx.Opcode.Bor, VIdx.Opcode.Bxor, VIdx.Opcode.Ishl, VIdx.Opcode.Ushr,
   VIdx.Opcode.Sshr, VIdx.Opcode.Rotl, VIdx.Opcode.Rotr, VIdx.Opcode.Smin, VIdx.Opcode.Smax,
   VIdx.Opcode.Umin, VIdx.Opcode.Umax,
   VIdx.Opcode.Udiv, VIdx.Opcode.Sdiv, VIdx.Opcode.Urem, VIdx.Opcode.Srem,
   VIdx.Opcode.Icmp, VIdx.Opcode.Uextend, VIdx.Opcode.Sextend, VIdx.Opcode.Ireduce,
   VIdx.Opcode.Load, VIdx.Opcode.Uload8, VIdx.Opcode.Sload8, VIdx.Opcode.Uload16,
   VIdx.Opcode.Sload16, VIdx.Opcode.Uload32, VIdx.Opcode.Sload32,
   VIdx.Opcode.Store, VIdx.Opcode.Istore8, VIdx.Opcode.Istore16, VIdx.Opcode.Istore32,
   VIdx.Opcode.Select, VIdx.Opcode.Nop, VIdx.Opcode.SymbolValue, VIdx.Opcode.StackAddr,
   VIdx.Opcode.Call, VIdx.Opcode.CallIndirect, VIdx.Opcode.FuncAddr,
   -- agent/atomics-proof
   VIdx.Opcode.Bmask, VIdx.Opcode.AtomicLoad, VIdx.Opcode.AtomicStore, VIdx.Opcode.AtomicRmw,
   VIdx.Opcode.AtomicCas, VIdx.Opcode.Fence,
   -- agent/stack-tls-proof
   VIdx.Opcode.TlsValue]

/-- The fields of the `InstructionData` of an E instruction with opcode `ko`, where the checker
needs them (`instData`): `uextend`/`sextend` have one value, `store` a value pair, flags and
an offset. -/
def opShape (ko : Nat) : Option (List AV) :=
  if ko == VIdx.Opcode.Uextend || ko == VIdx.Opcode.Sextend then some [.value]
  else if ko == VIdx.Opcode.Store then some [.values 2, .any, .any]
  else none

/-- The type extractors, on a type, independently of the context (`externExtract`). -/
def tyExtract (id : TermId) (t : CTy) : Option (ExtResult (List V)) :=
  match tyPred id with
  | some pr => some (if pr t then .ok [.ty t] else .fail)
  | none =>
    if id == TId.multi_lane then
      some (if t.laneCount > 1 then .ok [.int t.laneBits, .int t.laneCount] else .fail)
    else if id == TId.dynamic_lane then some .fail
    else none

/-- The extractors that fail on every instruction (disabled ISA flags). -/
def flagOff (id : TermId) : Bool :=
  id == TId.use_lse || id == TId.use_dotprod || id == TId.use_i8mm

/-- The ISLE type constant `$n` (`Sem.prim`, independent of the context). -/
def primTy (ty : TypeId) (n : String) : Option V :=
  if ty == TyId.Type then (CTy.ofName? n).map .ty else none

section
variable (p : Program)

mutual
/-- `q` cannot match any value that `a` describes. -/
def fails (a : AV) : Pattern → Bool
  | .bind _ _ q => fails a q
  | .and _ qs => failsAny a qs
  | .constPrim ty n =>
    match primTy ty n with
    | none => true
    | some c =>
      match a with
      | .tys ts => ts.all fun t => !(V.ty t == c)
      | .exact v => !(v == c)
      | _ => false
  | .term ty t args =>
    match termOf p t with
    | .error _ => true
    | .ok term =>
      match term.kind with
      | .enumVariant k =>
        match a with
        | .data =>
          match args with
          | .term _ oT [] :: rest =>
            match termOf p oT with
            | .error _ => true
            | .ok oterm =>
              match oterm.kind with
              | .enumVariant ko =>
                !(eOps.contains ko) ||
                  match opShape ko with
                  | some sh => failsArgs sh rest
                  | none => false
              | _ => false
          | _ => false
        | .exact v =>
          match v with
          | .data ty' k' fs => !(ty' == ty) || !(k == k') || failsArgs (fs.map .exact) args
          | _ => false
        | _ => false
      | .decl flags _ (some (.external _ _)) =>
        if flags.isMulti then true else
        match a with
        | .inst =>
          if term.id == TId.inst_data_value then failsArgs [.tys (.invalid :: eCTys), .data] args
          else flagOff term.id
        | .value =>
          if term.id == TId.def_inst then failsArgs [.inst] args
          else if term.id == TId.value_type then failsArgs [.tys eCTys] args
          else false
        | .values n =>
          if term.id == TId.value_array_2 && n == 2 then failsArgs [.value, .value] args
          else false
        | .tys ts =>
          ts.all fun t0 =>
            match tyExtract term.id t0 with
            | some (.ok fs) => failsArgs (fs.map .exact) args
            | some _ => true
            | none => false
        | .exact (.ty t0) =>
          match tyExtract term.id t0 with
          | some (.ok fs) => failsArgs (fs.map .exact) args
          | some _ => true
          | none => false
        | _ => false
      | _ => false
  | _ => false

/-- Some pattern of `qs` cannot match (an `and`). -/
def failsAny (a : AV) : List Pattern → Bool
  | [] => false
  | q :: qs => fails a q || failsAny a qs

/-- Some pattern of `qs` cannot match the value at its position. -/
def failsArgs : List AV → List Pattern → Bool
  | a :: as, q :: qs => fails a q || failsArgs as qs
  | _, _ => false
end

/-- The rule ids of the closure's root rules (`closureRoot`; `closureRoot_eq` checks the list
against `Closure.rules`). A literal, so that the kernel check of `exclOk` over the rule list
does not scan `Closure.rules` once per rule. -/
def closureRootIds : List Nat :=
  [582, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 745, 746, 747, 748, 749,
   756, 759, 777, 778, 779, 780, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798,
   799, 800, 802, 804, 806, 808, 810, 811, 815, 819, 824, 828, 833, 834, 836, 841, 842, 849, 854,
   855, 862, 863, 864, 869, 870, 873, 874, 883, 884, 890, 891, 892, 893, 899, 900, 901, 902, 903,
   904, 906, 907, 908, 909, 910, 911, 915, 916, 918, 919, 920, 922, 924, 925, 927, 932, 933, 934,
   936, 937, 938, 939, 940, 946, 958, 964, 971, 983, 984, 994, 995, 996, 997, 998, 999, 1000, 1001,
   1002, 1003, 1004, 1007, 1024, 1026, 1027, 1031, 1032, 1033, 1037, 1041, 1042, 1043, 1044,
   1052, 1053, 1054, 1055, 1056, 1057, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1093, 1129, 1130,
   1132, 1137,
   1138, 1139, 1140]

/-- A root rule of `lower` is in the closure or cannot match an instruction. -/
def exclOk (r : Rule) : Bool :=
  closureRootIds.contains r.id ||
    match r.args with
    | [q] => fails p .inst q
    | _ => false

end

end Backend.Proof
