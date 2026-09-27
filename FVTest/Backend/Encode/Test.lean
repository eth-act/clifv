import FV.Backend

/-!
# Encoder tests (`lake exe lean-backend-encode-test`, `docs/contracts/encoder.md`)

* `decode [FILE.clif...]` (default: `corpus/clif/*.clif`, `corpus/clif/extrt/*.clif` and
  Cranelift's `runtests/*.clif`): compile every file with the Lean backend, lay out every
  compiled function and check, for every instruction, that the Lean Arm model's decoder reads
  the encoded word back as the intended instruction:
  `decode_raw_inst (armBits a) = some a` where `a = toArmInst env i` (`Insn.decodeOk`), the
  executable form of the M5 theorem. Prints per-mnemonic counts and every failure.
* `random OUT.s OUT.o [--n N] [--seed S]`: for every instruction form of `Insn` (`forms`),
  `N` instances with random operands (every register including 31 in the roles that allow it,
  immediates over their whole ranges, all conditions, labels before and after the
  instruction, relocations with addends), plus jump-table words. Checks `Insn.decodeOk` on each,
  writes one function per form as assembly (`OUT.s`, for `llvm-mc`) and as a Lean-written
  object (`OUT.o`) for `scripts/lean-backend-encode-check.sh --random` to compare byte for byte.
  Also checks that the encoder's bitmask-immediate encoder accepts exactly the values
  `ImmLogic.ofNat?` (the isel's predicate) accepts.

Exit status 0 iff every check passes.
-/

open Backend Arm

/-! ## Decode check over compiled files -/

def defaultFiles : IO (List String) := do
  let mut out : Array String := #[]
  for dir in ["corpus/clif", "corpus/clif/extrt",
              "third_party/wasmtime/cranelift/filetests/filetests/runtests"] do
    let entries ← System.FilePath.readDir dir
    out := out ++ ((entries.filter (·.path.extension == some "clif")).map (·.path.toString)
      |>.qsort (· < ·))
  return out.toList

def mnemonic (i : Insn) : String := ((i.asm 0).splitOn " ").headD ""

/-- Add `k` to the count of `m`. -/
def bump (c : Std.HashMap String Nat) (m : String) : Std.HashMap String Nat :=
  c.insert m (c.getD m 0 + 1)

def decodeMain (files : List String) : IO UInt32 := do
  let files ← if files.isEmpty then defaultFiles else pure files
  let mut nfiles := 0
  let mut nfuncs := 0
  let mut ninsns := 0
  let mut nwords := 0
  let mut bad := 0
  let mut counts : Std.HashMap String Nat := {}
  for file in files do
    let fa := compileFile (Clif.parseFile (← IO.FS.readFile file))
    if fa.funcs.isEmpty then continue
    nfiles := nfiles + 1
    match fa.layout with
    | .error e =>
      IO.println s!"{file}: encoding failed: {e}"
      bad := bad + 1
    | .ok fbs =>
      for (f, fb) in fbs do
        nfuncs := nfuncs + 1
        nwords := nwords + fb.words.size
        let lbls := labelOffsets f.lines
        for (pc, i) in fb.insns do
          ninsns := ninsns + 1
          counts := bump counts (mnemonic i)
          if !i.decodeOk { pc, lbl := (lbls[·]?) } then
            bad := bad + 1
            let got := match i.encode { pc, lbl := (lbls[·]?) } with
              | .ok w => s!"{repr (decode_raw_inst w)}"
              | .error e => e
            IO.println s!"{file}: %{f.name}+{pc}: `{i.asm f.k}`: decode mismatch: {got}"
  let hist := counts.toList.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
  IO.println s!"mnemonics: {", ".intercalate (hist.toList.map fun (m, n) => s!"{m} {n}")}"
  IO.println s!"files {nfiles}, functions {nfuncs}, words {nwords}, instructions {ninsns} \
    ({hist.size} mnemonics): decode ok {ninsns - bad}, failures {bad}"
  return if bad == 0 && ninsns > 0 then 0 else 1

/-! ## Random operands -/

/-- xorshift64 state. -/
abbrev G := StateM UInt64

def rand (n : Nat) : G Nat := do
  let s ← get
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  set s
  pure (s.toNat % (max n 1))

def coin : G Bool := do pure ((← rand 2) == 1)

def pick [Inhabited α] (xs : List α) : G α := do pure (xs[← rand xs.length]!)

/-- Signed value in `[lo, hi]`. -/
def randInt (lo hi : Int) : G Int := do pure (lo + (← rand (hi - lo + 1).toNat))

/-- A register where 31 is ZR / SP; `gpr` never 31. -/
def gprZR : G Reg := do let k ← rand 32; pure (if k == 31 then .xzr else .x k)
def gprSP : G Reg := do let k ← rand 32; pure (if k == 31 then .sp else .x k)
def gpr : G Reg := do pure (.x (← rand 31))
def vr : G Reg := do pure (.v (← rand 32))
def randCond : G Cond := pick Cond.all
def nzcv : G NZCV := do pure ⟨← coin, ← coin, ← coin, ← coin⟩

/-- Labels `.block 0..7` are placed at random positions of each form's function. -/
def nLabels : Nat := 8
def label : G Lbl := do pure (.block (← rand nLabels))

/-- `DecodeBitMasks` forward (a random valid bitmask immediate at 32/64 bits). -/
def randBitmask (w : Bool) : G Nat := do
  let size := if w then 64 else 32
  let es := [2, 4, 8, 16, 32, 64].filter (· ≤ size)
  let e ← pick es
  let c := 1 + (← rand (e - 1))
  let r ← rand e
  let elem := rorN e (2 ^ c - 1) r
  pure ((List.range (size / e)).foldl (fun acc i => acc + elem * 2 ^ (e * i)) 0)

def sym : G String := pick ["ext_a", "ext_b", "form_b"]

/-- Load/store final addressing modes for an access of `bytes` bytes. -/
def amode (bytes : Nat) : G AMode := do
  match ← rand 7 with
  | 0 => pure (.unsignedOffset (← gprSP) (bytes * (← rand 4096)))
  | 1 => pure (.unscaled (← gprSP) (← randInt (-256) 255))
  | 2 => pure (.regReg (← gprSP) (← gprZR))
  | 3 => pure (.regScaled (← gprSP) (← gprZR))
  | 4 => pure (.regScaledExtended (← gprSP) (← gprZR) (← pick [.uxtw, .sxtw, .sxtx]))
  | 5 => pure (.regExtended (← gprSP) (← gprZR) (← pick [.uxtw, .sxtw, .sxtx]))
  | _ => if ← coin then pure (.spPreIndexed (← randInt (-256) 255))
         else pure (.spPostIndexed (← randInt (-256) 255))

def arith : List ALUOp := [.add, .sub, .addS, .subS]
def logic : List ALUOp := [.and, .andS, .andNot, .orr, .orrNot, .eor, .eorNot]

/-- One generator per instruction form. -/
def forms : List (String × G Insn) := [
  ("alu_rrr_arith_logic", do
    pure (.aluRRR (← pick (arith ++ logic)) (← coin) (← gprZR) (← gprZR) (← gprZR))),
  ("alu_rrr_div_shift", do
    pure (.aluRRR (← pick [.sDiv, .uDiv, .lsl, .lsr, .asr, .extr]) (← coin) (← gprZR) (← gprZR)
      (← gprZR))),
  ("alu_rrr_mulh", do pure (.aluRRR (← pick [.sMulH, .uMulH]) true (← gprZR) (← gprZR) (← gprZR))),
  ("alu_rrr_carry", do
    pure (.aluRRR (← pick [.adc, .adcS, .sbc, .sbcS]) (← coin) (← gprZR) (← gprZR) (← gprZR))),
  ("alu_rrrr", do
    pure (.aluRRRR (← pick [.mAdd, .mSub, .uMAddL, .sMAddL]) (← coin) (← gprZR) (← gprZR)
      (← gprZR) (← gprZR))),
  ("alu_imm12", do
    let op ← pick arith
    let rd ← if op == .add || op == .sub then gprSP else gprZR
    pure (.aluImm12 op (← coin) rd (← gprSP) ⟨← rand 4096, ← coin⟩)),
  ("logic_imm", do
    let op ← pick [.and, .orr, .eor, .andS]
    let w ← coin
    let rd ← if op == .andS then gprZR else gprSP
    pure (.logicImm op w rd (← gprZR) (← randBitmask w))),
  ("shift_imm", do
    let w ← coin
    pure (.shiftImm (← pick [.lsl, .lsr, .asr, .ror]) w (← gprZR) (← gprZR)
      (← rand (if w then 64 else 32)))),
  ("alu_rrr_shift", do
    let w ← coin
    let op ← pick (arith ++ logic)
    let sh ← if arith.contains op then pick [.lsl, .lsr, .asr] else pick [.lsl, .lsr, .asr, .ror]
    pure (.aluRRRShift op w (← gprZR) (← gprZR) (← gprZR) ⟨sh, ← rand (if w then 64 else 32)⟩)),
  ("extr", do
    let w ← coin
    pure (.extr w (← gprZR) (← gprZR) (← gprZR) (← rand (if w then 64 else 32)))),
  ("alu_rrr_extend", do
    let w ← coin
    let op ← pick arith
    let rd ← if op == .add || op == .sub then gprSP else gprZR
    let e ← if w then pick ExtendOp.all else pick [.uxtb, .uxth, .uxtw, .sxtb, .sxth, .sxtw]
    pure (.aluRRRExtend op w rd (← gprSP) (← gprZR) e)),
  ("bit_rr", do
    let w ← coin
    let op ← pick (if w then [.rbit, .clz, .cls, .rev16, .rev32, .rev64]
                   else [.rbit, .clz, .cls, .rev16, .rev64])
    pure (.bitRR op w (← gprZR) (← gprZR))),
  ("load", do
    let op ← pick [.uload8, .sload8, .uload16, .sload16, .uload32, .sload32, .uload64]
    pure (.load op (← gprZR) (← amode op.bytes))),
  ("store", do
    let op ← pick [.store8, .store16, .store32, .store64]
    pure (.store op (← gprZR) (← amode op.bytes))),
  ("load_store_q", do
    if ← coin then pure (.load .fpuLoad128 (← vr) (← amode 16))
    else pure (.store .fpuStore128 (← vr) (← amode 16))),
  ("ldp_stp", do
    let rt ← gprZR
    let rt2 ← gprZR
    let m ← if ← coin then pure (AMode.spPreIndexed (8 * (← randInt (-64) 63)))
            else pure (AMode.spPostIndexed (8 * (← randInt (-64) 63)))
    -- LDP with Rt = Rt2 is CONSTRAINED UNPREDICTABLE
    if ← coin then pure (.stp rt rt2 m)
    else pure (.ldp rt (if rt == rt2 then (if rt == .x 0 then .x 1 else .x 0) else rt2) m)),
  ("mov", do
    match ← rand 3 with
    | 0 => pure (.mov true .sp (← gpr))
    | 1 => pure (.mov true (← gpr) .sp)
    | _ => pure (.mov (← coin) (← gprZR) (← gprZR))),
  ("mov_wide", do
    let w ← coin
    pure (.movWide (← pick [.movZ, .movN]) w (← gprZR) ⟨← rand 65536, ← rand (if w then 4 else 2)⟩)),
  ("movk", do
    let w ← coin
    pure (.movk w (← gprZR) ⟨← rand 65536, ← rand (if w then 4 else 2)⟩)),
  ("bfm", do
    let w ← coin
    let size := if w then 64 else 32
    pure (.bfm (← pick [.sBfm, .uBfm]) w (← gprZR) (← gprZR) (← rand size) (← rand size))),
  ("cset", do pure (.cset (← gprZR) (← pick (Cond.all.filter fun c => c != .al && c != .nv)))),
  ("csel", do pure (.csel (← gprZR) (← gprZR) (← gprZR) (← randCond))),
  ("ccmp", do pure (.ccmp (← coin) (← gprZR) (← gprZR) (← nzcv) (← randCond))),
  ("ccmp_imm", do pure (.ccmpImm (← coin) (← gprZR) (← rand 32) (← nzcv) (← randCond))),
  ("fmov_to_fp", do pure (.fmovToFp (← pick [.size16, .size32, .size64]) (← vr) (← gprZR))),
  ("umov", do
    let s ← pick [ScalarSize.size8, .size16, .size32, .size64]
    let n := match s with | .size8 => 16 | .size16 => 8 | .size32 => 4 | _ => 2
    pure (.umov s (← gprZR) (← vr) (← rand n))),
  ("cnt", do pure (.cnt (← pick [.size8x8, .size8x16]) (← vr) (← vr))),
  ("vec_lanes", do
    pure (.vecLanes (← pick [.addv, .uaddlv]) (← pick [.size8x8, .size8x16, .size16x4, .size16x8,
      .size32x4]) (← vr) (← vr))),
  ("addp", do
    pure (.addp (← pick [.size8x8, .size8x16, .size16x4, .size16x8, .size32x2, .size32x4,
      .size64x2]) (← vr) (← vr) (← vr))),
  ("b", do pure (.b (← label))),
  ("bcond", do pure (.bcond (← randCond) (← label))),
  ("cbz", do pure (.cbz (← coin) (← coin) (← gprZR) (← label))),
  ("tbz", do pure (.tbz (← coin) (← gprZR) (← rand 64) (← label))),
  ("bl", do pure (.bl (← sym))),
  ("blr_br_ret", do
    match ← rand 3 with
    | 0 => pure (.blr (← gprZR))
    | 1 => pure (.br (← gprZR))
    | _ => pure .ret),
  ("udf", do pure (.udf (← rand 65536))),
  ("adr", do pure (.adr (← gprZR) (← label))),
  ("got", do
    if ← coin then pure (.adrpGot (← gprZR) (← sym)) else pure (.ldrGotLo12 (← gprZR) (← gprSP) (← sym))),
  ("near", do
    let a ← randInt (-4096) 4096
    if ← coin then pure (.adrp (← gprZR) (← sym) a) else pure (.addLo12 (← gprSP) (← gprSP) (← sym) a))
]

/-- The function of one form: `n` random instances, labels `.block 0..7` at random
positions, and (for the label forms) a jump table. -/
def formFunc (k : Nat) (name : String) (gen : G Insn) (n : Nat) : G FnAsm := do
  let mut lines : Array Line := #[]
  let pos ← (List.range nLabels).mapM fun _ => rand (n + 1)
  for j in [0:n + 1] do
    for (p, l) in pos.zipIdx do
      if p == j then lines := lines.push (.label (.block l))
    if j < n then lines := lines.push (.ins (← gen))
  -- a jump table after the code: `.word target - table` (data)
  lines := lines.push (.label (.jt 0))
  for l in [0:nLabels] do
    lines := lines.push (.word (.block l) (.jt 0))
  lines := lines.push (.ins .ret)
  let size := lines.foldl (fun s l => s + l.size) 0
  pure { name := s!"form_{name}", k, lines, size, traps := [] }

/-- Values on which the bitmask encoder must agree with `ImmLogic.ofNat?`. -/
def bitmaskSamples (n : Nat) : G (List (Bool × Nat)) := do
  let mut out := #[]
  for _ in [0:n] do
    let w ← coin
    let size := if w then 64 else 32
    let v ← match ← rand 3 with
      | 0 => randBitmask w
      | 1 => do pure ((← rand (2 ^ 32)) * 2 ^ 32 + (← rand (2 ^ 32)) % 2 ^ size)
      | _ => do pure ((← randBitmask w) ^^^ 2 ^ (← rand size))
    out := out.push (w, v % 2 ^ size)
  return out.toList

def randomMain (outS outO : String) (n seed : Nat) : IO UInt32 := do
  let gen : G (List FnAsm × List (Bool × Nat)) := do
    let fs ← forms.zipIdx.mapM fun ((name, g), k) => formFunc k name g n
    pure (fs, ← bitmaskSamples (20 * n))
  let ((fs, samples), _) := gen.run (UInt64.ofNat (seed ||| 1))
  let mut bad := 0
  let mut laid : Array (FnAsm × FnBin) := #[]
  for f in fs do
    match f.layout with
    | .error e => IO.println s!"{f.name}: encoding failed: {e}"; bad := bad + 1
    | .ok fb =>
      laid := laid.push (f, fb)
      let lbls := labelOffsets f.lines
      let mut ok := 0
      for (pc, i) in fb.insns do
        if i.decodeOk { pc, lbl := (lbls[·]?) } then ok := ok + 1
        else
          bad := bad + 1
          IO.println s!"{f.name}+{pc}: `{i.asm f.k}`: decode mismatch"
      IO.println s!"{f.name}: {fb.insns.size} instructions, decode ok {ok}"
  let mut bmBad := 0
  for (w, v) in samples do
    let isel := (ImmLogic.ofNat? v (if w then .size64 else .size32)).isSome
    if (bitmaskEnc? w v).isSome != isel then
      bmBad := bmBad + 1
      IO.println s!"bitmask disagreement: {if w then 64 else 32}-bit {hex v}: encoder \
        {(bitmaskEnc? w v).isSome}, ImmLogic.ofNat? {isel}"
  let accepted := (samples.filter fun (w, v) => (bitmaskEnc? w v).isSome).length
  IO.println s!"bitmask immediates: {samples.length} samples ({accepted} valid), \
    disagreements {bmBad}"
  IO.FS.writeFile outS ("  .text\n" ++ String.join (fs.map (·.text ++ "\n")))
  IO.FS.writeBinFile outO (elfObject laid.toList)
  let total := laid.foldl (fun s (_, fb) => s + fb.insns.size) 0
  IO.println s!"random: {fs.length} forms, {total} instructions, decode failures {bad}, seed {seed}"
  return if bad == 0 && bmBad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "decode" :: files => decodeMain files
  | "random" :: s :: o :: rest =>
    let rec opts (n seed : Nat) : List String → Option (Nat × Nat)
      | [] => some (n, seed)
      | "--n" :: k :: r => k.toNat?.bind fun k => opts k seed r
      | "--seed" :: k :: r => k.toNat?.bind fun k => opts n k r
      | _ => none
    match opts 200 0x5eed rest with
    | some (n, seed) => randomMain s o n seed
    | none => IO.eprintln "bad options"; return 2
  | _ =>
    IO.eprintln "usage: lean-backend-encode-test decode [FILE.clif...]"
    IO.eprintln "       lean-backend-encode-test random OUT.s OUT.o [--n N] [--seed S]"
    return 2
