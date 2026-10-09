import FV.Backend.Proof.StockImm

/-! A concrete named constant root, with selected-rule receipts. This fixture
executes the actual exported program at stock driver fuel. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096
private theorem selectRule_skipArgs {p : Program} {sem : Isle.Sem V State}
    {cfg : Config} {term : Term} {vs : List V} {s : State × Array RuleId}
    {pre : List Rule} (hn : ∀ r ∈ pre,
      matchArgs p sem s.1 r.args vs (Array.replicate r.vars.length none) = .ok none)
    (fuel : Nat) (post : List Rule) :
    (selectRule p sem cfg (fuel + pre.length + 2) term (pre ++ post) vs).run s =
      (selectRule p sem cfg (fuel + 2) term post vs).run s := by
  induction pre with
  | nil => rfl
  | cons r rs ih =>
    have hr := hn r (List.mem_cons_self ..)
    have htail := ih (fun r hr => hn r (List.mem_cons_of_mem _ hr))
    simp only [List.length_cons, List.cons_append]
    rw [show fuel + (rs.length + 1) + 2 = (fuel + rs.length) + 3 by omega]
    rw [selectRule.eq_3, tryRule.eq_2, matchRule.eq_2]
    simp only [isel_monad, hr]
    exact htail

private structure NopExtraData (p : Program) : Prop where
  t129 : termOf p 129 = .ok T.«ty_float_or_vec»
  t137 : termOf p 137 = .ok T.«ty_vec64_int»
  t138 : termOf p 138 = .ok T.«ty_vec128_int»
  t313 : termOf p 313 = .ok T.«use_lse»
  t314 : termOf p 314 = .ok T.«use_dotprod»
  t315 : termOf p 315 = .ok T.«use_i8mm»
  t2294 : termOf p 2294 = .ok T.«Opcode.ReturnCall»
  t2302 : termOf p 2302 = .ok T.«Opcode.Insertlane»
  t2303 : termOf p 2303 = .ok T.«Opcode.Extractlane»
  t2342 : termOf p 2342 = .ok T.«Opcode.F16const»
  t2343 : termOf p 2343 = .ok T.«Opcode.F32const»
  t2344 : termOf p 2344 = .ok T.«Opcode.F64const»
  t2345 : termOf p 2345 = .ok T.«Opcode.F128const»
  t2346 : termOf p 2346 = .ok T.«Opcode.Vconst»
  t2347 : termOf p 2347 = .ok T.«Opcode.Shuffle»
  t2351 : termOf p 2351 = .ok T.«Opcode.Bitselect»
  t2360 : termOf p 2360 = .ok T.«Opcode.Iabs»
  t2373 : termOf p 2373 = .ok T.«Opcode.SaddOverflow»
  t2374 : termOf p 2374 = .ok T.«Opcode.UsubOverflow»
  t2375 : termOf p 2375 = .ok T.«Opcode.SsubOverflow»
  t2402 : termOf p 2402 = .ok T.«Opcode.Fma»
  t2412 : termOf p 2412 = .ok T.«Opcode.Bitcast»
  t2416 : termOf p 2416 = .ok T.«Opcode.Snarrow»
  t2417 : termOf p 2417 = .ok T.«Opcode.Unarrow»
  t2418 : termOf p 2418 = .ok T.«Opcode.Uunarrow»
  t2420 : termOf p 2420 = .ok T.«Opcode.SwidenHigh»
  t2422 : termOf p 2422 = .ok T.«Opcode.UwidenHigh»
  t2431 : termOf p 2431 = .ok T.«Opcode.FcvtToUint»
  t2432 : termOf p 2432 = .ok T.«Opcode.FcvtToSint»
  t2433 : termOf p 2433 = .ok T.«Opcode.FcvtToUintSat»
  t2434 : termOf p 2434 = .ok T.«Opcode.FcvtToSintSat»
  t2436 : termOf p 2436 = .ok T.«Opcode.FcvtFromUint»
  t2437 : termOf p 2437 = .ok T.«Opcode.FcvtFromSint»
  t2438 : termOf p 2438 = .ok T.«Opcode.Isplit»
  t2450 : termOf p 2450 = .ok T.«InstructionData.BinaryImm8»
  t2467 : termOf p 2467 = .ok T.«InstructionData.Shuffle»
  t2472 : termOf p 2472 = .ok T.«InstructionData.TernaryImm8»
  t2477 : termOf p 2477 = .ok T.«InstructionData.UnaryConst»
  t2479 : termOf p 2479 = .ok T.«InstructionData.UnaryIeee16»
  t2480 : termOf p 2480 = .ok T.«InstructionData.UnaryIeee32»
  t2481 : termOf p 2481 = .ok T.«InstructionData.UnaryIeee64»

set_option maxRecDepth 100000 in
private theorem nopExtraData_program : NopExtraData program :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def iconstCtx : Ctx :=
  (fun {f : Clif.Function} {ctx : Ctx} (_ : MappedCtxInv f ctx) => ctx)
    buildCtx_mappedInv_witness.2.2.1

private def iconstPrefix : List Rule :=
  [rule_lower_419, rule_lower_402, rule_lower_1444, rule_lower_1481, rule_lower_116, rule_lower_125,
    rule_lower_1442, rule_lower_1479, rule_lower_2779, rule_lower_120, rule_lower_128, rule_lower_165,
    rule_lower_1439, rule_lower_1476, rule_lower_2784, rule_lower_93, rule_lower_167, rule_lower_1437,
    rule_lower_1474, rule_lower_1501, rule_lower_1507, rule_lower_2789, rule_lower_3091, rule_lower_3155,
    rule_lower_90, rule_lower_169, rule_lower_1435, rule_lower_1472, rule_lower_1540, rule_lower_2152,
    rule_lower_2793, rule_lower_3097, rule_lower_3161, rule_lower_102, rule_lower_171, rule_lower_1408,
    rule_lower_1434, rule_lower_1471, rule_lower_1539, rule_lower_2158, rule_lower_2185, rule_lower_2798,
    rule_lower_2828, rule_lower_3008, rule_lower_3101, rule_lower_3165, rule_lower_98, rule_lower_190,
    rule_lower_437, rule_lower_609, rule_lower_810, rule_lower_861, rule_lower_1163, rule_lower_1222,
    rule_lower_1224, rule_lower_1226, rule_lower_1228, rule_lower_1406, rule_lower_1431, rule_lower_1468,
    rule_lower_1536, rule_lower_2120, rule_lower_2164, rule_lower_2191, rule_lower_2386, rule_lower_2404,
    rule_lower_2419, rule_lower_2435, rule_lower_2815, rule_lower_3018, rule_lower_3036, rule_lower_3056,
    rule_lower_3076, rule_lower_3126, rule_lower_3140, rule_lower_3190, rule_lower_3204, rule_lower_111,
    rule_lower_203, rule_lower_205, rule_lower_207, rule_lower_209, rule_lower_211, rule_lower_213,
    rule_lower_215, rule_lower_217, rule_lower_222, rule_lower_224, rule_lower_226, rule_lower_228,
    rule_lower_230, rule_lower_232, rule_lower_240, rule_lower_242, rule_lower_244, rule_lower_246,
    rule_lower_248, rule_lower_250, rule_lower_260, rule_lower_262, rule_lower_264, rule_lower_266,
    rule_lower_268, rule_lower_270, rule_lower_294, rule_lower_300, rule_lower_440, rule_lower_608,
    rule_lower_693, rule_lower_699, rule_lower_707, rule_lower_713, rule_lower_730, rule_lower_733,
    rule_lower_750, rule_lower_753, rule_lower_767, rule_lower_773, rule_lower_787, rule_lower_793,
    rule_lower_816, rule_lower_857, rule_lower_1056, rule_lower_1068, rule_lower_1116, rule_lower_1167,
    rule_lower_1236, rule_lower_1242, rule_lower_1248, rule_lower_1254, rule_lower_1266, rule_lower_1272,
    rule_lower_1281, rule_lower_1283, rule_lower_1401, rule_lower_1429, rule_lower_1466, rule_lower_1534,
    rule_lower_1704, rule_lower_1707, rule_lower_1803, rule_lower_1808, rule_lower_2138, rule_lower_2170,
    rule_lower_2197, rule_lower_2288, rule_lower_2328, rule_lower_2331, rule_lower_2334, rule_lower_2337,
    rule_lower_2340, rule_lower_2343, rule_lower_2346, rule_lower_2349, rule_lower_2352, rule_lower_2381,
    rule_lower_2400, rule_lower_2415, rule_lower_2431, rule_lower_2451, rule_lower_2466, rule_lower_2508,
    rule_lower_2580, rule_lower_2803, rule_lower_2822, rule_lower_2837, rule_lower_3014, rule_lower_3031,
    rule_lower_3051, rule_lower_3071, rule_lower_3110, rule_lower_3174]

set_option maxHeartbeats 4000000 in
private theorem iconst_prefix_nomatch {p : Program} (hp : Data p) (hx : NopExtraData p) (ctx : Ctx) (hdata : ∀ st : LState, Backend.externExtract ctx T.inst_data_value (.inst 0) st =
      .ok [.ty (.int 8), .data 152 35 [.data 151 57 [], .int 9]]) (st : State) :
    ∀ r ∈ iconstPrefix, matchArgs p (Stock.sem ctx) st r.args [.inst 0]
      (Array.replicate r.vars.length none) = .ok none := by
  have hfit (st : LState) : Backend.externExtract ctx T.fits_in_64 (.ty (.int 8)) st =
      .ok [.ty (.int 8)] := rfl
  intro r hr
  simp only [iconstPrefix, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [matchArgs, matchPat, matchAll, isel_data, isel_monad,
    hp.t110, hp.t111, hp.t113, hp.t119, hp.t120, hp.t126, hp.t128, hx.t129,
    hp.t132, hp.t133, hx.t137, hx.t138, hp.t152,
    hp.t205, hp.t209, hx.t313, hx.t314, hx.t315,
    hp.t340, hp.t2292, hx.t2294, hx.t2302,
    hx.t2303, hp.t2304, hp.t2305, hp.t2306, hp.t2307, hx.t2346, hx.t2347, hx.t2351, hp.t2356, hp.t2357, hp.t2358, hp.t2359, hx.t2360,
    hp.t2362, hp.t2363, hp.t2366, hp.t2367, hp.t2372, hx.t2373, hx.t2374, hx.t2375,
    hp.t2376, hp.t2377, hp.t2381, hp.t2382, hp.t2383, hp.t2384, hp.t2385, hp.t2388,
    hp.t2389, hp.t2396, hx.t2402, hx.t2412, hx.t2416, hx.t2417, hx.t2418, hx.t2420, hx.t2422, hp.t2425, hx.t2431, hx.t2432, hx.t2433,
    hx.t2434, hx.t2436, hx.t2437, hx.t2438, hp.t2440, hp.t2441, hp.t2447, hp.t2448,
    hp.t2449, hx.t2450, hp.t2453, hp.t2458, hp.t2461, hp.t2464, hx.t2467, hp.t2471, hx.t2472,
    hp.t2476, hx.t2477, Stock.sem, Backend.sem, hdata, hfit,
    rule_lower_419, rule_lower_402, rule_lower_1444, rule_lower_1481, rule_lower_116, rule_lower_125,
    rule_lower_1442, rule_lower_1479, rule_lower_2779, rule_lower_120, rule_lower_128,
    rule_lower_165, rule_lower_1439, rule_lower_1476, rule_lower_2784, rule_lower_93,
    rule_lower_167, rule_lower_1437, rule_lower_1474, rule_lower_1501, rule_lower_1507,
    rule_lower_2789, rule_lower_3091, rule_lower_3155, rule_lower_90, rule_lower_169,
    rule_lower_1435, rule_lower_1472, rule_lower_1540, rule_lower_2152, rule_lower_2793,
    rule_lower_3097, rule_lower_3161, rule_lower_102, rule_lower_171, rule_lower_1408,
    rule_lower_1434, rule_lower_1471, rule_lower_1539, rule_lower_2158, rule_lower_2185,
    rule_lower_2798, rule_lower_2828, rule_lower_3008, rule_lower_3101, rule_lower_3165,
    rule_lower_98, rule_lower_190, rule_lower_437, rule_lower_609, rule_lower_810, rule_lower_861,
    rule_lower_1163, rule_lower_1222, rule_lower_1224, rule_lower_1226, rule_lower_1228,
    rule_lower_1406, rule_lower_1431, rule_lower_1468, rule_lower_1536, rule_lower_2120,
    rule_lower_2164, rule_lower_2191, rule_lower_2386, rule_lower_2404, rule_lower_2419,
    rule_lower_2435, rule_lower_2815, rule_lower_3018, rule_lower_3036, rule_lower_3056,
    rule_lower_3076, rule_lower_3126, rule_lower_3140, rule_lower_3190, rule_lower_3204,
    rule_lower_111, rule_lower_203, rule_lower_205, rule_lower_207, rule_lower_209, rule_lower_211,
    rule_lower_213, rule_lower_215, rule_lower_217, rule_lower_222, rule_lower_224, rule_lower_226,
    rule_lower_228, rule_lower_230, rule_lower_232, rule_lower_240, rule_lower_242, rule_lower_244,
    rule_lower_246, rule_lower_248, rule_lower_250, rule_lower_260, rule_lower_262, rule_lower_264,
    rule_lower_266, rule_lower_268, rule_lower_270, rule_lower_294, rule_lower_300, rule_lower_440,
    rule_lower_608, rule_lower_693, rule_lower_699, rule_lower_707, rule_lower_713, rule_lower_730,
    rule_lower_733, rule_lower_750, rule_lower_753, rule_lower_767, rule_lower_773, rule_lower_787,
    rule_lower_793, rule_lower_816, rule_lower_857, rule_lower_1056, rule_lower_1068,
    rule_lower_1116, rule_lower_1167, rule_lower_1236, rule_lower_1242, rule_lower_1248,
    rule_lower_1254, rule_lower_1266, rule_lower_1272, rule_lower_1281, rule_lower_1283,
    rule_lower_1401, rule_lower_1429, rule_lower_1466, rule_lower_1534, rule_lower_1704,
    rule_lower_1707, rule_lower_1803, rule_lower_1808, rule_lower_2138, rule_lower_2170,
    rule_lower_2197, rule_lower_2288, rule_lower_2328, rule_lower_2331, rule_lower_2334,
    rule_lower_2337, rule_lower_2340, rule_lower_2343, rule_lower_2346, rule_lower_2349,
    rule_lower_2352, rule_lower_2381, rule_lower_2400, rule_lower_2415, rule_lower_2431,
    rule_lower_2451, rule_lower_2466, rule_lower_2508, rule_lower_2580, rule_lower_2803,
    rule_lower_2822, rule_lower_2837, rule_lower_3014, rule_lower_3031, rule_lower_3051,
    rule_lower_3071, rule_lower_3110, rule_lower_3174]
  all_goals rfl


private theorem iconst_args {p : Program} (hp : Data p) (ctx : Ctx) (hdata : ∀ st : LState, Backend.externExtract ctx T.inst_data_value (.inst 0) st =
      .ok [.ty (.int 8), .data 152 35 [.data 151 57 [], .int 9]]) (st : State) :
    matchArgs p (Stock.sem ctx) st rule_lower_53.args [.inst 0]
      (Array.replicate rule_lower_53.vars.length none) =
        .ok (some (env2 (.ty (.int 8)) (.int 9))) := by
  have hu (st : LState) : Backend.externExtract ctx T.u64_from_imm64 (.int 9) st =
      .ok [.int 9] := rfl
  isel_eval [hp.t209, hp.t2482, hp.t2341, hp.t144, hdata, hu, Stock.sem, rule_lower_53]

private theorem iconst_apply {p : Program} (hp : Data p) (hx : NopExtraData p) (ctx : Ctx) (hdata : ∀ st : LState, Backend.externExtract ctx T.inst_data_value (.inst 0) st =
      .ok [.ty (.int 8), .data 152 35 [.data 151 57 [], .int 9]]) (st : State) :
    ∃ (next : State) (trace : Array RuleId),
      (applyTerm p (Stock.sem ctx) {} 1000000
        T.lower.ret T.lower.id [.inst 0]).run (st, #[]) =
          .ok (some (.regsVec [[(st.base.fresh .int).1]]), next, trace.push 582) ∧
      (evalExpr p (Stock.sem ctx) {} 999999 rule_lower_53.rhs
        (env2 (.ty (.int 8)) (.int 9))).run (st, #[]) =
          .ok (some (.regsVec [[(st.base.fresh .int).1]]), next, trace) ∧
      (matchRule p (Stock.sem ctx) {} 999825 rule_lower_53 [.inst 0]).run
        (st, #[]) = .ok (some (env2 (.ty (.int 8)) (.int 9)), st, #[]) := by
  obtain ⟨next, trace, hrhs⟩ := stock_iconst_rhs_nine_large hp ctx st
  have hmatch : (matchRule p (Stock.sem ctx) {} 999825 rule_lower_53
      [.inst 0]).run (st, #[]) =
        .ok (some (env2 (.ty (.int 8)) (.int 9)), st, #[]) := by
    have ha := iconst_args hp ctx hdata st
    rw [matchRule.eq_2]
    simp only [M.run_bind, M.run_get, M.except_ok_bind, ha,
      show rule_lower_53.iflets = [] from rfl, matchIfLets.eq_2, isel_monad]
  refine ⟨next, trace, ?_, hrhs, hmatch⟩
  change (applyTerm p (Stock.sem ctx) {} 1000000 25 686 [.inst 0]).run (st, #[]) = _
  rw [applyTerm_internal_run hp.t686 term_686_kind rfl]
  have hrs : p.rulesOf 686 = iconstPrefix ++ rule_lower_53 :: (p.rulesOf 686).drop 173 := by
    rw [hp.r686]
    rfl
  rw [hrs]
  have hskip := selectRule_skipArgs (iconst_prefix_nomatch hp hx ctx hdata st)
    (cfg := {}) (term := T.lower) (s := (st, #[]))
    999825 (rule_lower_53 :: (p.rulesOf 686).drop 173)
  change (selectRule p (Stock.sem ctx) {} 999999 T.lower
      (iconstPrefix ++ rule_lower_53 :: (p.rulesOf 686).drop 173) [.inst 0]).run
        (st, #[]) = _ at hskip
  rw [hskip]
  have hselect : (selectRule p (Stock.sem ctx) {} 999827 T.lower
      (rule_lower_53 :: (p.rulesOf 686).drop 173) [.inst 0]).run (st, #[]) =
        .ok (some (rule_lower_53, env2 (.ty (.int 8)) (.int 9)), st, #[]) := by
    rw [selectRule.eq_3, tryRule.eq_2]
    simp only [M.run_bind, M.run_get, M.except_ok_bind, hmatch, isel_monad]
  rw [hselect]
  simp only [M.except_ok_bind, M.run_bind]
  rw [hrhs]
  simp only [isel_monad, rule_lower_53]

private theorem iconst_run (st : State) :
    ∃ (next : State) (trace : Array RuleId),
      Stock.runTerm iconstCtx "lower" [.inst 0] st =
        .ok (some (.regsVec [[(st.base.fresh .int).1]]), next, (trace.push 582).toList) := by
  obtain ⟨next, trace, ha, _, _⟩ := iconst_apply data_program nopExtraData_program iconstCtx (fun _ => rfl) st
  refine ⟨next, trace, ?_⟩
  unfold Stock.runTerm Interp.run
  rw [program_termByName_lower]
  dsimp only
  rw [ha]
  rfl

/-- The actual generated named entry selects this constant rule; its full
state is exactly the state produced by the selected RHS, not only its base. -/
theorem stock_statement_selectedConstant :
    ∃ (f : Clif.Function) (ctx : Ctx) (info : IInfo),
      MappedCtxInv f ctx ∧ ctx.insts[0]? = some info ∧
      info.clif = some (.iconst .i8 9) ∧ info.results = [2] ∧
      ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      ∀ st, ∃ (next : State) (trace : Array RuleId),
        Stock.runTerm ctx "lower" [.inst 0] st =
          .ok (some (.regsVec [[(st.base.fresh .int).1]]), next, (trace.push 582).toList) ∧
        (evalExpr program (Stock.sem ctx) {} 999999 rule_lower_53.rhs
          (env2 (.ty (.int 8)) (.int 9))).run (st, #[]) =
            .ok (some (.regsVec [[(st.base.fresh .int).1]]), next, trace) ∧
        (matchRule program (Stock.sem ctx) {} 999825 rule_lower_53 [.inst 0]).run (st, #[]) =
          .ok (some (env2 (.ty (.int 8)) (.int 9)), st, #[]) := by
  obtain ⟨_, _, hctx, hmap⟩ := buildCtx_mappedInv_witness
  refine ⟨_, iconstCtx, iconstCtx.insts[0]!, hctx, rfl, rfl, rfl, hmap, ?_⟩
  intro st
  obtain ⟨next, trace, ha, he, hm⟩ := iconst_apply data_program nopExtraData_program iconstCtx (fun _ => rfl) st
  refine ⟨next, trace, ?_, he, hm⟩
  unfold Stock.runTerm Interp.run
  rw [program_termByName_lower]
  dsimp only
  rw [ha]
  rfl

theorem stock_statement_selectedConstant_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (info : IInfo) (next : State) (trace : Array RuleId),
      MappedCtxInv f ctx ∧ info.results = [2] ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      Stock.runTerm ctx "lower" [.inst 0] sinkState =
        .ok (some (.regsVec [[.vreg 194 .int]]), next, (trace.push 582).toList) ∧
      (evalExpr program (Stock.sem ctx) {} 999999 rule_lower_53.rhs
        (env2 (.ty (.int 8)) (.int 9))).run (sinkState, #[]) =
          .ok (some (.regsVec [[.vreg 194 .int]]), next, trace) ∧
      (matchRule program (Stock.sem ctx) {} 999825 rule_lower_53 [.inst 0]).run (sinkState, #[]) =
        .ok (some (env2 (.ty (.int 8)) (.int 9)), sinkState, #[]) := by
  obtain ⟨f, ctx, info, hc, hi, hic, hres, hmap, hrun⟩ := stock_statement_selectedConstant
  obtain ⟨next, trace, hr, he, hm⟩ := hrun sinkState
  exact ⟨f, ctx, info, next, trace, hc, hres, hmap, hr, he, hm⟩

/-- Successful context construction and source scope for the concrete generated
constant root, together with its actual interpreter execution. -/
theorem stock_statement_selectedConstant_built :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State)
      (info : IInfo), LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧
      info.results = [2] ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      ∀ st, ∃ (next : State) (trace : Array RuleId),
        (applyTerm program (Stock.sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst 0]).run
          (st, #[]) = .ok (some (.regsVec [[(st.base.fresh .int).1]]), next, trace.push 582) := by
  obtain ⟨scope, built, _, mapped⟩ := buildCtx_mappedInv_witness
  refine ⟨_, iconstCtx, _, _, iconstCtx.insts[0]!, scope, built, rfl, rfl, rfl, mapped, ?_⟩
  intro st
  obtain ⟨next, trace, run, _, _⟩ := iconst_apply data_program nopExtraData_program iconstCtx (fun _ => rfl) st
  exact ⟨next, trace, run⟩

theorem stock_statement_selectedConstant_built_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State)
      (info : IInfo) (next : State) (trace : Array RuleId),
      LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧
      info.results = [2] ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      (applyTerm program (Stock.sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst 0]).run
        (sinkState, #[]) = .ok (some (.regsVec [[.vreg 194 .int]]), next, trace.push 582) := by
  obtain ⟨f, ctx, ranges, initial, info, scope, built, hi, hc, results, mapped, run⟩ :=
    stock_statement_selectedConstant_built
  obtain ⟨next, trace, actual⟩ := run sinkState
  exact ⟨f, ctx, ranges, initial, info, next, trace, scope, built, hi, hc, results, mapped, actual⟩

/-- The real generated constant root depends on its source data, not on the
terminator data or exception reservations elsewhere in the context. -/
theorem stock_statement_selectedConstant_context (ctx : Ctx)
    (data : ∀ st : LState, Backend.externExtract ctx T.inst_data_value (.inst 0) st =
      .ok [.ty (.int 8), .data 152 35 [.data 151 57 [], .int 9]]) (st : State) :
    ∃ (next : State) (trace : Array RuleId),
      (applyTerm program (Stock.sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst 0]).run
        (st, #[]) = .ok (some (.regsVec [[(st.base.fresh .int).1]]), next, trace.push 582) := by
  obtain ⟨next, trace, run, _, _⟩ := iconst_apply data_program nopExtraData_program ctx data st
  exact ⟨next, trace, run⟩

private def selectedReserved : List Reg × List Reg :=
  ([.vreg 194 .int], [.vreg 195 .int, .vreg 196 .int])
private def selectedData : V := (Backend.termData (.ret [2])).toOption.getD (.op .unit)
private def selectedCtx : Ctx :=
  { Driver.termCtx iconstCtx 1 selectedData with tryRegs := selectedReserved }
private def selectedInput : State :=
  { sinkState with base := { sinkState.base with nextVreg := 197 } }

/-- Actual driver-fuel generated lowering executes after changing the real
terminator placeholder to return data and installing nonempty exception reserves. -/
theorem stock_statement_selectedConstant_context_witness :
    ∃ (next : State) (trace : Array RuleId),
      iconstCtx.valueReg? 2 = some (.vreg 193 .int) ∧
      selectedCtx.insts[1]? ≠ iconstCtx.insts[1]? ∧ selectedCtx.tryRegs.2 ≠ [] ∧
      (applyTerm program (Stock.sem selectedCtx) {} 1000000 T.lower.ret T.lower.id [.inst 0]).run
        (selectedInput, #[]) = .ok (some (.regsVec [[.vreg 197 .int]]), next, trace.push 582) := by
  obtain ⟨next, trace, run⟩ := stock_statement_selectedConstant_context selectedCtx (fun _ => rfl) selectedInput
  refine ⟨next, trace, rfl, ?_, (by decide), run⟩
  intro same
  have data := congrArg (fun q => q.map (·.data)) same
  cases data

end Backend.Stock.Proof
