/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

# Untrusted AArch64 decoder and symbolic stepper (value numbering)

Covers the instruction forms Cranelift 0.136.1 emits for the integer subset
(`docs/contracts/arm.md`, "Required instructions"). Used only to decide what the generated
proof claims; the proof itself steps the LNSym model.
-/
import FV.Validate.Gen.Sym

namespace Validate.Gen

/-- Bits `[lo, lo+n)` of `w`. -/
def bits (w : UInt32) (lo n : Nat) : Nat := (w.toNat >>> lo) % (2 ^ n)

def sext (n : Nat) (x : Nat) : Int := if x ≥ 2 ^ (n - 1) then (x : Int) - 2 ^ n else x

/-- Shift kinds of shifted-register operands. -/
inductive ShiftK | lsl | lsr | asr | ror deriving Inhabited, BEq

def ShiftK.ofNat : Nat → ShiftK | 0 => .lsl | 1 => .lsr | 2 => .asr | _ => .ror

/-- Decoded instruction (only what the symbolic stepper needs). -/
inductive AI where
  | addSubImm (sf sub setf : Bool) (imm : Nat) (rn rd : Nat)
  | addSubShift (sf sub setf : Bool) (sh : ShiftK) (amt rm rn rd : Nat)
  | addSubExt (sf sub setf : Bool) (option imm3 rm rn rd : Nat)
  | adcSbc (sf sub setf : Bool) (rm rn rd : Nat)
  | logImm (sf : Bool) (opc : Nat) (imm : BitVec 64) (rn rd : Nat)
  | logShift (sf : Bool) (opc : Nat) (neg : Bool) (sh : ShiftK) (amt rm rn rd : Nat)
  | movWide (sf : Bool) (opc hw imm16 rd : Nat)
  | bitfield (sf : Bool) (opc immr imms rn rd : Nat)
  | extr (sf : Bool) (rm lsb rn rd : Nat)
  | adr (page : Bool) (imm : Int) (rd : Nat)
  | dp2 (sf : Bool) (opc rm rn rd : Nat)
  | dp1 (sf : Bool) (opc rn rd : Nat)
  | dp3 (sf : Bool) (kind : Nat) (rm ra rn rd : Nat)  -- 0 madd 1 msub 2 smulh 3 umulh
  | csel (sf : Bool) (kind cond rm rn rd : Nat)        -- 0 csel 1 csinc 2 csinv 3 csneg
  | ccmp (sf neg isImm : Bool) (cond rmImm rn nzcv : Nat)
  | b (off : Int) | bl (off : Int) | bcond (cond : Nat) (off : Int)
  | cbz (sf nz : Bool) (rt : Nat) (off : Int)
  | tbz (nz : Bool) (bit rt : Nat) (off : Int)
  | br (rn : Nat) | blr (rn : Nat) | ret (rn : Nat)
  | udf | nop
  /-- Single-register load/store. `mode`: 0 offset, 1 post-index, 2 pre-index.
  `ext`: 0 zero-extend, 1 sign-extend to 64, 2 sign-extend to 32. `off` in bytes. -/
  | ldst (load : Bool) (size : Nat) (ext : Nat) (mode : Nat) (off : Int) (rn rt : Nat)
  /-- Register-offset load/store: address `Xn + extend(Rm) << amt`. -/
  | ldstReg (load : Bool) (size ext : Nat) (rm option amt rn rt : Nat)
  /-- Load/store pair (`size` = 4 or 8 bytes per register, `sx` = LDPSW). -/
  | ldstPair (load : Bool) (size : Nat) (sx : Bool) (mode : Nat) (off : Int) (rn rt rt2 : Nat)
  deriving Inhabited

/-- `DecodeBitMasks` (immediate forms of logical instructions). -/
def decodeBitMask (sf : Bool) (n immr imms : Nat) : Option (BitVec 64) := do
  let combined := (n <<< 6) ||| (0x3f - (imms &&& 0x3f))
  let len ← (List.range 7).reverse.find? fun i => (combined >>> i) &&& 1 == 1
  if len < 1 then none
  let esize := 2 ^ len
  let levels := esize - 1
  let s := imms &&& levels
  let r := immr &&& levels
  if s == levels then none
  let welem : Nat := 2 ^ (s + 1) - 1
  -- rotate right by r within esize bits
  let rot := ((welem >>> r) ||| (welem <<< (esize - r))) % 2 ^ esize
  let width := if sf then 64 else 32
  let mut v : Nat := 0
  for i in [0:width / esize] do
    v := v ||| (rot <<< (i * esize))
  pure (BitVec.ofNat 64 v)

def decode (w : UInt32) : Option AI :=
  let sf := bits w 31 1 == 1
  let rd := bits w 0 5
  let rn := bits w 5 5
  let rm := bits w 16 5
  if w == 0xd503201f || w == 0xd503229f || w == 0xd503233f || w == 0xd503241f then some .nop
  else if bits w 16 16 == 0 then some .udf
  -- add/sub immediate
  else if bits w 23 6 == 0b100010 then
    let imm := bits w 10 12 <<< (if bits w 22 1 == 1 then 12 else 0)
    some (.addSubImm sf (bits w 30 1 == 1) (bits w 29 1 == 1) imm rn rd)
  -- logical immediate
  else if bits w 23 6 == 0b100100 then
    match decodeBitMask sf (bits w 22 1) (bits w 16 6) (bits w 10 6) with
    | some imm => some (.logImm sf (bits w 29 2) imm rn rd)
    | none => none
  else if bits w 23 6 == 0b100101 then some (.movWide sf (bits w 29 2) (bits w 21 2) (bits w 5 16) rd)
  else if bits w 23 6 == 0b100110 then
    some (.bitfield sf (bits w 29 2) (bits w 16 6) (bits w 10 6) rn rd)
  else if bits w 23 6 == 0b100111 && bits w 29 2 == 0 then some (.extr sf rm (bits w 10 6) rn rd)
  else if bits w 24 5 == 0b10000 then
    let imm := (bits w 5 19 <<< 2) ||| bits w 29 2
    let page := bits w 31 1 == 1
    some (.adr page (sext 21 imm * (if page then 4096 else 1)) rd)
  -- logical shifted register
  else if bits w 24 5 == 0b01010 then
    some (.logShift sf (bits w 29 2) (bits w 21 1 == 1) (ShiftK.ofNat (bits w 22 2)) (bits w 10 6) rm rn rd)
  -- add/sub shifted / extended register
  else if bits w 24 5 == 0b01011 then
    if bits w 21 1 == 0 then
      some (.addSubShift sf (bits w 30 1 == 1) (bits w 29 1 == 1) (ShiftK.ofNat (bits w 22 2)) (bits w 10 6) rm rn rd)
    else some (.addSubExt sf (bits w 30 1 == 1) (bits w 29 1 == 1) (bits w 13 3) (bits w 10 3) rm rn rd)
  else if bits w 21 8 == 0b11010000 && bits w 10 6 == 0 then
    some (.adcSbc sf (bits w 30 1 == 1) (bits w 29 1 == 1) rm rn rd)
  else if bits w 21 8 == 0b11010010 && bits w 29 1 == 1 && bits w 10 1 == 0 && bits w 4 1 == 0 then
    some (.ccmp sf (bits w 30 1 == 0) (bits w 11 1 == 1) (bits w 12 4) rm rn (bits w 0 4))
  else if bits w 21 8 == 0b11010100 && bits w 29 1 == 0 && bits w 11 1 == 0 then
    some (.csel sf ((bits w 30 1 <<< 1) ||| bits w 10 1) (bits w 12 4) rm rn rd)
  else if bits w 21 8 == 0b11010110 && bits w 29 2 == 0 then some (.dp2 sf (bits w 10 6) rm rn rd)
  else if bits w 21 8 == 0b11010110 && bits w 29 2 == 0b10 && bits w 16 5 == 0 then
    some (.dp1 sf (bits w 10 6) rn rd)
  else if bits w 24 5 == 0b11011 && bits w 29 2 == 0 then
    let op31 := bits w 21 3
    let o0 := bits w 15 1
    let ra := bits w 10 5
    if op31 == 0 then some (.dp3 sf o0 rm ra rn rd)
    else if op31 == 0b010 && o0 == 0 then some (.dp3 sf 2 rm ra rn rd)
    else if op31 == 0b110 && o0 == 0 then some (.dp3 sf 3 rm ra rn rd)
    else none
  -- branches
  else if bits w 26 6 == 0b000101 then some (.b (sext 26 (bits w 0 26) * 4))
  else if bits w 26 6 == 0b100101 then some (.bl (sext 26 (bits w 0 26) * 4))
  else if bits w 24 8 == 0b01010100 && bits w 4 1 == 0 then
    some (.bcond (bits w 0 4) (sext 19 (bits w 5 19) * 4))
  else if bits w 25 6 == 0b011010 then
    some (.cbz sf (bits w 24 1 == 1) (bits w 0 5) (sext 19 (bits w 5 19) * 4))
  else if bits w 25 6 == 0b011011 then
    some (.tbz (bits w 24 1 == 1) ((bits w 31 1 <<< 5) ||| bits w 19 5) (bits w 0 5) (sext 14 (bits w 5 14) * 4))
  else if w &&& 0xfffffc1f == 0xd61f0000 then some (.br rn)
  else if w &&& 0xfffffc1f == 0xd63f0000 then some (.blr rn)
  else if w &&& 0xfffffc1f == 0xd65f0000 then some (.ret rn)
  -- loads and stores (general registers only)
  else if bits w 27 3 == 0b111 && bits w 26 1 == 0 then
    let size := bits w 30 2
    let opc := bits w 22 2
    let (load, ext) := match opc with
      | 0 => (false, 0) | 1 => (true, 0) | 2 => (true, 1) | _ => (true, 2)
    if size == 3 && opc ≥ 2 then none
    else if size == 2 && opc == 3 then none
    else if bits w 24 2 == 0b01 then
      some (.ldst load size ext 0 (bits w 10 12 * 2 ^ size) rn rd)
    else if bits w 24 2 == 0 && bits w 21 1 == 0 then
      let mode := bits w 10 2
      let imm := sext 9 (bits w 12 9)
      if mode == 0 then some (.ldst load size ext 0 imm rn rd)
      else if mode == 1 then some (.ldst load size ext 1 imm rn rd)
      else if mode == 3 then some (.ldst load size ext 2 imm rn rd)
      else none
    else if bits w 24 2 == 0 && bits w 21 1 == 1 && bits w 10 2 == 0b10 then
      some (.ldstReg load size ext rm (bits w 13 3) (if bits w 12 1 == 1 then size else 0) rn rd)
    else none
  else if bits w 27 3 == 0b101 && bits w 26 1 == 0 then
    let opc := bits w 30 2
    let load := bits w 22 1 == 1
    let mode := bits w 23 3
    let size : Nat := if opc == 2 then 8 else 4
    let sx := opc == 1
    let off := sext 7 (bits w 15 7) * (size : Int)
    let m := if mode == 0b010 then some 0 else if mode == 0b001 then some 1
      else if mode == 0b011 then some 2 else none
    match m with
    | some m => if opc == 3 || (sx && !load) then none
      else some (.ldstPair load size sx m off rn rd (bits w 10 5))
    | none => none
  else none

/-! ## Symbolic state -/

/-- A memory write (address node, bytes, value node). -/
structure Store where
  addr : Nat
  n : Nat
  val : Nat
  deriving Inhabited

/-- Symbolic Arm state: register nodes (index 31 is SP), the flags (a node whose bits 3..0 are
N Z C V), and the memory writes since the last cut point (the first ones restate what the
cut point knows about the stack). -/
structure AState where
  regs : Array Nat
  nzcv : Nat
  stores : Array Store
  deriving Inhabited

/-- Byte `i` of the base memory of sample `k` (a hash). -/
def baseByte (k : Nat) (a : BitVec 64) : BitVec 8 :=
  let h : UInt64 := (a.toNat.toUInt64 * (0x9E3779B97F4A7C15 : UInt64)) ^^^ (k.toUInt64 * (0xC2B2AE3D27D4EB4F : UInt64))
  let h := h ^^^ (h >>> 29)
  BitVec.ofNat 8 ((h * (0xBF58476D1CE4E5B9 : UInt64)) >>> 56).toNat

/-- Read `n` bytes at `a` in sample `k` through the writes `st`. -/
def readMem (st : Array (BitVec 64 × Nat × BitVec 64)) (k : Nat) (a : BitVec 64) (n : Nat) :
    BitVec 64 := Id.run do
  let mut v : BitVec 64 := 0
  for i in [0:n] do
    let x := a + BitVec.ofNat 64 i
    let mut b := baseByte k x
    for (sa, sn, sv) in st do
      let d := x - sa
      if d.toNat < sn then b := (sv >>> (8 * d.toNat)).setWidth 8
    v := v ||| ((b.setWidth 64) <<< (8 * i))
  v

/-- Load `n` bytes at node `addr` in state `s`. -/
def loadNode (s : AState) (addr n : Nat) : SymM Nat := do
  let va ← vals addr
  let mut sts : Array (Array (BitVec 64 × Nat × BitVec 64)) := Array.replicate nSamples #[]
  for st in s.stores do
    let sa ← vals st.addr
    let sv ← vals st.val
    for k in [0:nSamples] do
      sts := sts.modify k (·.push (sa[k]!, st.n, sv[k]!))
  let mut vs := #[]
  for k in [0:nSamples] do
    vs := vs.push (readMem sts[k]! k va[k]! n)
  addNode { shape := .other, vals := vs }

/-! ## Bit-vector helpers on 64-bit containers -/

def mask (sf : Bool) (x : BitVec 64) : BitVec 64 := if sf then x else maskW 32 x
def width (sf : Bool) : Nat := if sf then 64 else 32

/-- `AddWithCarry` at width `n`: (result, NZCV). -/
def addWithCarry (n : Nat) (x y : BitVec 64) (c : Nat) : BitVec 64 × BitVec 64 :=
  let xu := (maskW n x).toNat
  let yu := (maskW n y).toNat
  let us := xu + yu + c
  let res := maskW n (BitVec.ofNat 64 us)
  let sx := if xu ≥ 2 ^ (n - 1) then (xu : Int) - 2 ^ n else xu
  let sy := if yu ≥ 2 ^ (n - 1) then (yu : Int) - 2 ^ n else yu
  let ss := sx + sy + c
  let rs := if res.toNat ≥ 2 ^ (n - 1) then (res.toNat : Int) - 2 ^ n else res.toNat
  let nf := if res.toNat ≥ 2 ^ (n - 1) then 8 else 0
  let zf := if res.toNat == 0 then 4 else 0
  let cf := if us ≥ 2 ^ n then 2 else 0
  let vf := if rs != ss then 1 else 0
  (res, BitVec.ofNat 64 (nf + zf + cf + vf))

def condHolds (cond : Nat) (nzcv : BitVec 64) : Bool :=
  let n := nzcv.getLsbD 3
  let z := nzcv.getLsbD 2
  let c := nzcv.getLsbD 1
  let v := nzcv.getLsbD 0
  let r := match cond / 2 with
    | 0 => z | 1 => c | 2 => n | 3 => v | 4 => c && !z | 5 => n == v | 6 => n == v && !z
    | _ => true
  if cond % 2 == 1 && cond != 15 then !r else r

def shiftVal (n : Nat) (k : ShiftK) (x : BitVec 64) (amt : Nat) : BitVec 64 :=
  let x := maskW n x
  let a := amt % n
  match k with
  | .lsl => maskW n (x <<< a)
  | .lsr => x >>> a
  | .asr => maskW n (BitVec.ofInt 64 ((if x.toNat ≥ 2 ^ (n - 1) then (x.toNat : Int) - 2 ^ n else x.toNat) >>> a))
  | .ror => maskW n ((x >>> a) ||| (x <<< (n - a)))

def sextFrom (n : Nat) (x : BitVec 64) : BitVec 64 :=
  let x := maskW n x
  if n ≥ 64 then x else if x.toNat ≥ 2 ^ (n - 1) then x - BitVec.ofNat 64 (2 ^ n) else x

def extendReg (option : Nat) (x : BitVec 64) : BitVec 64 :=
  match option with
  | 0 => maskW 8 x | 1 => maskW 16 x | 2 => maskW 32 x | 3 => x
  | 4 => sextFrom 8 x | 5 => sextFrom 16 x | 6 => sextFrom 32 x | _ => x

end Validate.Gen

namespace Validate.Gen

/-- A memory access of one instruction. `val` is the stored value, or the raw loaded bytes. -/
structure MemEv where
  load : Bool
  addr : Nat
  n : Nat
  val : Nat
  deriving Inhabited

/-- Control flow after an instruction. Offsets are relative to the instruction. -/
inductive Flow where
  | seq
  | jump (off : Int)
  /-- Taken (to `off`) iff node `c` is non-zero. -/
  | cond (c : Nat) (off : Int)
  | indirect (target : Nat)
  /-- `bl off` / `blr`: call; `target` is the callee address node (for `blr`). -/
  | callDirect (off : Int)
  | callReg (target : Nat)
  | ret (target : Nat)
  | udf
  deriving Inhabited

structure StepOut where
  st : AState
  mems : Array MemEv := #[]
  flow : Flow := .seq

section
variable (s : AState)

def rdZ (i : Nat) : SymM Nat := if i == 31 then mkConst 0 else pure s.regs[i]!
def rdSP (i : Nat) : SymM Nat := pure s.regs[i]!

def wrZ (i : Nat) (v : Nat) (sf : Bool) : SymM AState := do
  if i == 31 then return s
  let v ← if sf then pure v else op1 (maskW 32) v
  return { s with regs := s.regs.set! i v }

def wrSP (i : Nat) (v : Nat) (sf : Bool) : SymM AState := do
  let v ← if sf then pure v else op1 (maskW 32) v
  return { s with regs := s.regs.set! i v }
end

def rbitW (n : Nat) (a : BitVec 64) : BitVec 64 := Id.run do
  let mut v : BitVec 64 := 0
  for i in [0:n] do
    if a.getLsbD i then v := v ||| (1#64 <<< (n - 1 - i))
  return v

def clzW (n : Nat) (a : BitVec 64) : BitVec 64 := Id.run do
  let a := maskW n a
  let mut c := n
  for i in [0:n] do
    if a.getLsbD i then c := n - 1 - i
  return BitVec.ofNat 64 c

/-- Execute one decoded instruction symbolically. -/
def stepAI (s : AState) : AI → SymM StepOut
  | .nop => pure { st := s }
  | .udf => pure { st := s, flow := .udf }
  | .addSubImm sf sub setf imm rn rd => do
    let x ← rdSP s rn
    let n := width sf
    let y := BitVec.ofNat 64 imm
    let (yv, c) := if sub then (~~~y, 1) else (y, 0)
    let r ← if !setf && rn == 31 || (!setf && !sub) then
        (if sf then addConst x (if sub then 0 - y else y) else op1 (fun a => (addWithCarry n a yv c).1) x)
      else op1 (fun a => (addWithCarry n a yv c).1) x
    let s ← if setf then do
        let f ← op1 (fun a => (addWithCarry n a yv c).2) x
        let s ← wrZ s rd r sf
        pure { s with nzcv := f }
      else wrSP s rd r sf
    pure { st := s }
  | .addSubShift sf sub setf sh amt rm rn rd => do
    let n := width sf
    let x ← rdZ s rn
    let y0 ← rdZ s rm
    let y ← op1 (fun v => shiftVal n sh v amt) y0
    let c := if sub then 1 else 0
    let r ← op2 (fun a b => (addWithCarry n a (if sub then ~~~b else b) c).1) x y
    if setf then
      let f ← op2 (fun a b => (addWithCarry n a (if sub then ~~~b else b) c).2) x y
      let s ← wrZ s rd r sf
      pure { st := { s with nzcv := f } }
    else pure { st := ← wrZ s rd r sf }
  | .addSubExt sf sub setf option imm3 rm rn rd => do
    let n := width sf
    let x ← rdSP s rn
    let y0 ← rdZ s rm
    let y ← op1 (fun v => maskW n (extendReg option v <<< imm3)) y0
    let c := if sub then 1 else 0
    let r ← op2 (fun a b => (addWithCarry n a (if sub then ~~~b else b) c).1) x y
    if setf then
      let f ← op2 (fun a b => (addWithCarry n a (if sub then ~~~b else b) c).2) x y
      let s ← wrZ s rd r sf
      pure { st := { s with nzcv := f } }
    else pure { st := ← wrSP s rd r sf }
  | .adcSbc sf sub setf rm rn rd => do
    let n := width sf
    let x ← rdZ s rn
    let y ← rdZ s rm
    let r ← op3 (fun a b f => (addWithCarry n a (if sub then ~~~b else b) (if f.getLsbD 1 then 1 else 0)).1) x y s.nzcv
    if setf then
      let f ← op3 (fun a b f => (addWithCarry n a (if sub then ~~~b else b) (if f.getLsbD 1 then 1 else 0)).2) x y s.nzcv
      let s ← wrZ s rd r sf
      pure { st := { s with nzcv := f } }
    else pure { st := ← wrZ s rd r sf }
  | .logImm sf opc imm rn rd => do
    let x ← rdZ s rn
    let r ← op1 (fun a => mask sf (match opc with
      | 0 => a &&& imm | 1 => a ||| imm | 2 => a ^^^ imm | _ => a &&& imm)) x
    if opc == 3 then
      let f ← op1 (fun v => BitVec.ofNat 64 ((if v.getLsbD (width sf - 1) then 8 else 0) + (if v == 0 then 4 else 0))) r
      let s ← wrZ s rd r sf
      pure { st := { s with nzcv := f } }
    else pure { st := ← wrSP s rd r sf }
  | .logShift sf opc neg sh amt rm rn rd => do
    let n := width sf
    let x ← rdZ s rn
    let y ← rdZ s rm
    let r ← op2 (fun a b =>
      let b := shiftVal n sh b amt
      let b := if neg then maskW n (~~~b) else b
      mask sf (match opc with | 0 => a &&& b | 1 => a ||| b | 2 => a ^^^ b | _ => a &&& b)) x y
    if opc == 3 then
      let f ← op1 (fun v => BitVec.ofNat 64 ((if v.getLsbD (n - 1) then 8 else 0) + (if v == 0 then 4 else 0))) r
      let s ← wrZ s rd r sf
      pure { st := { s with nzcv := f } }
    else pure { st := ← wrZ s rd r sf }
  | .movWide sf opc hw imm16 rd => do
    let v := BitVec.ofNat 64 (imm16 <<< (16 * hw))
    match opc with
    | 0 => pure { st := ← wrZ s rd (← mkConst (mask sf (~~~v))) sf }
    | 2 => pure { st := ← wrZ s rd (← mkConst v) sf }
    | 3 =>
      let x ← rdZ s rd
      let m : BitVec 64 := ~~~(BitVec.ofNat 64 (0xffff <<< (16 * hw)))
      pure { st := ← wrZ s rd (← op1 (fun a => (a &&& m) ||| v) x) sf }
    | _ => fail "movw"
  | .bitfield sf opc immr imms rn rd => do
    let n := width sf
    let x ← rdZ s rn
    let old ← rdZ s rd
    -- ASL: DecodeBitMasks(N, imms, immr, FALSE) → (wmask, tmask)
    let f := fun (src dst : BitVec 64) =>
      let src := maskW n src
      if imms ≥ immr then
        -- field [immr, imms] of src → [0, imms-immr]
        let len := imms - immr + 1
        let fld := maskW len (src >>> immr)
        match opc with
        | 0 => maskW n (sextFrom len fld)
        | 2 => fld
        | _ => maskW n ((dst &&& ~~~(maskW len (BitVec.allOnes 64))) ||| fld)
      else
        -- field [0, imms] of src → [n-immr, n-immr+imms]
        let len := imms + 1
        let pos := n - immr
        let fld := maskW len src
        match opc with
        | 0 => maskW n (sextFrom (pos + len) (fld <<< pos))
        | 2 => maskW n (fld <<< pos)
        | _ =>
          let m := maskW n ((maskW len (BitVec.allOnes 64)) <<< pos)
          maskW n ((dst &&& ~~~m) ||| (fld <<< pos))
    pure { st := ← wrZ s rd (← op2 f x old) sf }
  | .extr sf rm lsb rn rd => do
    let n := width sf
    let hi ← rdZ s rn
    let lo ← rdZ s rm
    let r ← op2 (fun h l =>
      if lsb == 0 then maskW n l else maskW n ((maskW n l >>> lsb) ||| (maskW n h <<< (n - lsb)))) hi lo
    pure { st := ← wrZ s rd r sf }
  | .adr _ _ _ => fail "adr/adrp handled by the caller"
  | .dp2 sf opc rm rn rd => do
    let n := width sf
    let x ← rdZ s rn
    let y ← rdZ s rm
    let r ← match opc with
      | 2 => op2 (fun a b => let a := maskW n a; let b := maskW n b; if b == 0 then 0 else a / b) x y
      | 3 => op2 (fun a b =>
          let a := maskW n a; let b := maskW n b
          if b == 0 then 0 else
          let ia : Int := if a.toNat ≥ 2 ^ (n - 1) then (a.toNat : Int) - 2 ^ n else a.toNat
          let ib : Int := if b.toNat ≥ 2 ^ (n - 1) then (b.toNat : Int) - 2 ^ n else b.toNat
          maskW n (BitVec.ofInt 64 (ia.tdiv ib))) x y
      | 8 => op2 (fun a b => shiftVal n .lsl a (maskW n b).toNat) x y
      | 9 => op2 (fun a b => shiftVal n .lsr a (maskW n b).toNat) x y
      | 10 => op2 (fun a b => shiftVal n .asr a (maskW n b).toNat) x y
      | 11 => op2 (fun a b => shiftVal n .ror a (maskW n b).toNat) x y
      | _ => fail s!"dp2 opcode {opc}"
    pure { st := ← wrZ s rd r sf }
  | .dp1 sf opc rn rd => do
    let n := width sf
    let x ← rdZ s rn
    let r ← match opc with
      | 0 => op1 (rbitW n) x
      | 4 => op1 (clzW n) x
      | _ => fail s!"dp1 opcode {opc}"
    pure { st := ← wrZ s rd r sf }
  | .dp3 sf kind rm ra rn rd => do
    let n := width sf
    let x ← rdZ s rn
    let y ← rdZ s rm
    let z ← rdZ s ra
    let r ← match kind with
      | 0 => op3 (fun a b c => maskW n (c + a * b)) x y z
      | 1 => op3 (fun a b c => maskW n (c - a * b)) x y z
      | 2 => op2 (fun a b => BitVec.ofInt 64 ((a.toInt * b.toInt) >>> 64)) x y
      | _ => op2 (fun a b => BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)) x y
    pure { st := ← wrZ s rd r sf }
  | .csel sf kind cond rm rn rd => do
    let n := width sf
    let x ← rdZ s rn
    let y ← rdZ s rm
    let r ← op3 (fun f a b =>
      if condHolds cond f then maskW n a else
      match kind with
      | 0 => maskW n b | 1 => maskW n (b + 1) | 2 => maskW n (~~~b) | _ => maskW n (0 - b)) s.nzcv x y
    pure { st := ← wrZ s rd r sf }
  | .ccmp sf neg isImm cond rmImm rn nzcv => do
    let n := width sf
    let x ← rdZ s rn
    let y ← if isImm then mkConst (BitVec.ofNat 64 rmImm) else rdZ s rmImm
    let f ← op3 (fun f a b =>
      if condHolds cond f then (addWithCarry n a (if neg then ~~~b else b) (if neg then 1 else 0)).2
      else BitVec.ofNat 64 nzcv) s.nzcv x y
    pure { st := { s with nzcv := f } }
  | .b off => pure { st := s, flow := .jump off }
  | .bl off => pure { st := s, flow := .callDirect off }
  | .bcond cond off => do
    let c ← op1 (fun f => if condHolds cond f then 1 else 0) s.nzcv
    pure { st := s, flow := .cond c off }
  | .cbz sf nz rt off => do
    let x ← rdZ s rt
    let c ← op1 (fun a => if (mask sf a == 0) != nz then 1 else 0) x
    pure { st := s, flow := .cond c off }
  | .tbz nz bit rt off => do
    let x ← rdZ s rt
    let c ← op1 (fun a => if a.getLsbD bit == nz then 1 else 0) x
    pure { st := s, flow := .cond c off }
  | .br rn => do pure { st := s, flow := .indirect (← rdZ s rn) }
  | .blr rn => do pure { st := s, flow := .callReg (← rdZ s rn) }
  | .ret rn => do pure { st := s, flow := .ret (← rdZ s rn) }
  | .ldst load size ext mode off rn rt => do
    let n := 2 ^ size
    let base ← rdSP s rn
    let addr ← if mode == 1 then pure base else addConst base (BitVec.ofInt 64 off)
    let s ← if mode == 0 then pure s else
      pure { s with regs := s.regs.set! rn (← addConst base (BitVec.ofInt 64 off)) }
    if load then
      let raw ← loadNode s addr n
      let v ← match ext with
        | 0 => pure raw
        | 1 => op1 (sextFrom (8 * n)) raw
        | _ => op1 (fun a => maskW 32 (sextFrom (8 * n) a)) raw
      pure { st := ← wrZ s rt v true, mems := #[{ load := true, addr, n, val := raw }] }
    else
      let v ← rdZ s rt
      let v ← op1 (maskW (8 * n)) v
      let s := { s with stores := s.stores.push { addr, n, val := v } }
      pure { st := s, mems := #[{ load := false, addr, n, val := v }] }
  | .ldstReg load size ext rm option amt rn rt => do
    let n := 2 ^ size
    let base ← rdSP s rn
    let idx ← rdZ s rm
    let addr ← op2 (fun b i => b + (extendReg option i <<< amt)) base idx
    if load then
      let raw ← loadNode s addr n
      let v ← match ext with
        | 0 => pure raw
        | 1 => op1 (sextFrom (8 * n)) raw
        | _ => op1 (fun a => maskW 32 (sextFrom (8 * n) a)) raw
      pure { st := ← wrZ s rt v true, mems := #[{ load := true, addr, n, val := raw }] }
    else
      let v ← rdZ s rt
      let v ← op1 (maskW (8 * n)) v
      let s := { s with stores := s.stores.push { addr, n, val := v } }
      pure { st := s, mems := #[{ load := false, addr, n, val := v }] }
  | .ldstPair load size sx mode off rn rt rt2 => do
    let base ← rdSP s rn
    let addr ← if mode == 1 then pure base else addConst base (BitVec.ofInt 64 off)
    let addr2 ← addConst addr (BitVec.ofNat 64 size)
    let s ← if mode == 0 then pure s else
      pure { s with regs := s.regs.set! rn (← addConst base (BitVec.ofInt 64 off)) }
    if load then
      let r1 ← loadNode s addr size
      let r2 ← loadNode s addr2 size
      let v1 ← if sx then op1 (sextFrom 32) r1 else pure r1
      let v2 ← if sx then op1 (sextFrom 32) r2 else pure r2
      let s ← wrZ s rt v1 true
      let s ← wrZ s rt2 v2 true
      pure { st := s, mems := #[{ load := true, addr, n := size, val := r1 },
        { load := true, addr := addr2, n := size, val := r2 }] }
    else
      let v1 ← op1 (maskW (8 * size)) (← rdZ s rt)
      let v2 ← op1 (maskW (8 * size)) (← rdZ s rt2)
      let st1 : Store := { addr, n := size, val := v1 }
      let st2 : Store := { addr := addr2, n := size, val := v2 }
      let s := { s with stores := (s.stores.push st1).push st2 }
      pure { st := s, mems := #[{ load := false, addr, n := size, val := v1 },
        { load := false, addr := addr2, n := size, val := v2 }] }

end Validate.Gen
