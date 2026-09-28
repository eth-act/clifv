import FV.Opt.Proof.RuleArith
import FV.Opt.Proof.RuleCprop
import FV.Opt.Proof.RuleSkel
import FV.Opt.Optimize

/-!
# The proven allow-list is sound

`simplifyRulesCorrect_proven`: every `simplify` rule of `Isle.Opt.program` whose id is in
`Opt.provenSimplifyRules` is `RuleOk`. `simplifySound_proven`: the Cranelift rule set with the
`proven` allow-list is a sound rule set (`Opt.SimplifySound`), the obligation the `simplify`
pass proof takes (`Opt.Config.simplifyFn` with `ruleAllow := .proven`).

The rule list of `simplify` is only inspected through `List.filter` on rule ids (`rfl`: the
kernel reads each rule's `id` field, nothing else); the rules themselves are handled by the
per-rule theorems over an abstract program with `Data p` (`data_program`).
-/

namespace Opt.Proof

open Isle Isle.Opt

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The `simplify` rules in the proven allow-list. -/
theorem simplify_rules_proven :
    (program.rulesOf T.«simplify».id).filter (fun r => RuleAllow.proven.pred r.id) =
      [rule_arithmetic_8, rule_arithmetic_13, rule_arithmetic_18, rule_arithmetic_24,
        rule_arithmetic_26, rule_arithmetic_28, rule_arithmetic_31, rule_arithmetic_35,
        rule_arithmetic_59, rule_arithmetic_233, rule_arithmetic_239, rule_arithmetic_240,
        rule_arithmetic_243, rule_arithmetic_244, rule_arithmetic_247, rule_arithmetic_295,
        rule_arithmetic_296, rule_arithmetic_297, rule_arithmetic_298, rule_arithmetic_301,
        rule_arithmetic_302, rule_arithmetic_303, rule_arithmetic_304, rule_arithmetic_307,
        rule_arithmetic_308, rule_arithmetic_311, rule_arithmetic_312, rule_arithmetic_313,
        rule_arithmetic_314, rule_arithmetic_317, rule_arithmetic_318, rule_arithmetic_319,
        rule_arithmetic_320, rule_arithmetic_323, rule_arithmetic_324, rule_arithmetic_337,
        rule_arithmetic_338, rule_arithmetic_339, rule_arithmetic_340, rule_arithmetic_346,
        rule_arithmetic_352, rule_arithmetic_353, rule_arithmetic_354, rule_arithmetic_355,
        rule_arithmetic_356, rule_arithmetic_357, rule_arithmetic_358, rule_arithmetic_359,
        rule_arithmetic_362, rule_arithmetic_363, rule_arithmetic_364, rule_arithmetic_365,
        rule_arithmetic_366, rule_arithmetic_367, rule_arithmetic_368, rule_arithmetic_369,
        rule_arithmetic_372, rule_arithmetic_373, rule_arithmetic_374, rule_arithmetic_375,
        rule_arithmetic_378, rule_arithmetic_379, rule_arithmetic_380, rule_arithmetic_381,
        rule_arithmetic_384, rule_arithmetic_385, rule_arithmetic_388, rule_arithmetic_389,
        rule_arithmetic_390, rule_arithmetic_391, rule_arithmetic_424, rule_arithmetic_451,
        rule_arithmetic_452, rule_arithmetic_453, rule_arithmetic_454, rule_arithmetic_457,
        rule_arithmetic_458, rule_arithmetic_459, rule_arithmetic_460, rule_arithmetic_461,
        rule_arithmetic_462, rule_arithmetic_463, rule_arithmetic_464, rule_arithmetic_467,
        rule_arithmetic_468, rule_arithmetic_469, rule_arithmetic_470, rule_arithmetic_471,
        rule_arithmetic_472, rule_arithmetic_473, rule_arithmetic_474, rule_arithmetic_477,
        rule_arithmetic_478, rule_arithmetic_479, rule_arithmetic_480, rule_arithmetic_481,
        rule_arithmetic_482, rule_arithmetic_483, rule_arithmetic_484, rule_arithmetic_485,
        rule_arithmetic_486, rule_arithmetic_487, rule_arithmetic_488, rule_arithmetic_489,
        rule_arithmetic_490, rule_arithmetic_491, rule_arithmetic_492, rule_arithmetic_495,
        rule_arithmetic_496, rule_arithmetic_497, rule_arithmetic_498, rule_arithmetic_500,
        rule_arithmetic_501, rule_arithmetic_502, rule_arithmetic_503, rule_arithmetic_505,
        rule_arithmetic_506, rule_arithmetic_507, rule_arithmetic_508, rule_arithmetic_510,
        rule_arithmetic_511, rule_arithmetic_512, rule_arithmetic_513, rule_arithmetic_515,
        rule_arithmetic_516, rule_arithmetic_517, rule_arithmetic_518, rule_arithmetic_520,
        rule_arithmetic_521, rule_arithmetic_522, rule_arithmetic_523, rule_arithmetic_525,
        rule_arithmetic_526, rule_arithmetic_527, rule_arithmetic_528, rule_arithmetic_530,
        rule_arithmetic_531, rule_arithmetic_532, rule_arithmetic_533, rule_arithmetic_536,
        rule_arithmetic_537, rule_arithmetic_538, rule_arithmetic_539, rule_arithmetic_541,
        rule_arithmetic_542, rule_arithmetic_543, rule_arithmetic_544, rule_arithmetic_546,
        rule_arithmetic_547, rule_arithmetic_548, rule_arithmetic_549, rule_arithmetic_551,
        rule_arithmetic_552, rule_arithmetic_553, rule_arithmetic_554, rule_arithmetic_556,
        rule_arithmetic_557, rule_arithmetic_558, rule_arithmetic_559, rule_arithmetic_561,
        rule_arithmetic_562, rule_arithmetic_563, rule_arithmetic_564, rule_arithmetic_566,
        rule_arithmetic_567, rule_arithmetic_568, rule_arithmetic_569, rule_arithmetic_571,
        rule_arithmetic_572, rule_arithmetic_573, rule_arithmetic_574, rule_arithmetic_599,
        rule_cprop_3, rule_cprop_9, rule_cprop_14, rule_cprop_20, rule_cprop_26,
        rule_cprop_56, rule_cprop_62, rule_cprop_68, rule_cprop_74, rule_cprop_104,
        rule_cprop_109, rule_cprop_114, rule_cprop_119, rule_cprop_147, rule_cprop_152,
        rule_cprop_155, rule_cprop_159, rule_cprop_162, rule_cprop_165, rule_cprop_169,
        rule_cprop_170, rule_cprop_171, rule_cprop_172, rule_cprop_174, rule_cprop_183,
        rule_cprop_193, rule_cprop_197, rule_cprop_201, rule_cprop_205, rule_cprop_209,
        rule_cprop_214, rule_cprop_217, rule_cprop_220, rule_cprop_223, rule_cprop_227,
        rule_cprop_229, rule_cprop_232, rule_cprop_235, rule_cprop_238, rule_cprop_241,
        rule_cprop_247, rule_cprop_249, rule_cprop_252, rule_cprop_254, rule_cprop_257,
        rule_cprop_259, rule_cprop_333, rule_cprop_337, rule_cprop_341, rule_cprop_345,
        rule_cprop_349, rule_cprop_521] := by
  rfl

set_option maxRecDepth 20000 in
theorem simplify_rules_length : (program.rulesOf T.«simplify».id).length = 1281 := by
  rfl

/-- Every rule of a list is `RuleOk` (a conjunction, built from the per-rule theorems). -/
def AllOk : List Rule → Prop
  | [] => True
  | r :: rs => RuleOk program r ∧ AllOk rs

theorem AllOk.mem : ∀ {rs : List Rule}, AllOk rs → ∀ r ∈ rs, RuleOk program r
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, hs⟩, r, .tail _ hm => AllOk.mem hs r hm

set_option maxRecDepth 20000 in
/-- Every rule of the proven list is `RuleOk`. -/
theorem proven_rules_ok : AllOk
    ((program.rulesOf T.«simplify».id).filter (fun r => RuleAllow.proven.pred r.id)) := by
  rw [simplify_rules_proven]
  exact ⟨ok_rule_arithmetic_8 data_program,
    ok_rule_arithmetic_13 data_program,
    ok_rule_arithmetic_18 data_program,
    ok_rule_arithmetic_24 data_program,
    ok_rule_arithmetic_26 data_program,
    ok_rule_arithmetic_28 data_program,
    ok_rule_arithmetic_31 data_program,
    ok_rule_arithmetic_35 data_program,
    ok_rule_arithmetic_59 data_program,
    ok_rule_arithmetic_233 data_program,
    ok_rule_arithmetic_239 data_program,
    ok_rule_arithmetic_240 data_program,
    ok_rule_arithmetic_243 data_program,
    ok_rule_arithmetic_244 data_program,
    ok_rule_arithmetic_247 data_program,
    ok_rule_arithmetic_295 data_program,
    ok_rule_arithmetic_296 data_program,
    ok_rule_arithmetic_297 data_program,
    ok_rule_arithmetic_298 data_program,
    ok_rule_arithmetic_301 data_program,
    ok_rule_arithmetic_302 data_program,
    ok_rule_arithmetic_303 data_program,
    ok_rule_arithmetic_304 data_program,
    ok_rule_arithmetic_307 data_program,
    ok_rule_arithmetic_308 data_program,
    ok_rule_arithmetic_311 data_program,
    ok_rule_arithmetic_312 data_program,
    ok_rule_arithmetic_313 data_program,
    ok_rule_arithmetic_314 data_program,
    ok_rule_arithmetic_317 data_program,
    ok_rule_arithmetic_318 data_program,
    ok_rule_arithmetic_319 data_program,
    ok_rule_arithmetic_320 data_program,
    ok_rule_arithmetic_323 data_program,
    ok_rule_arithmetic_324 data_program,
    ok_rule_arithmetic_337 data_program,
    ok_rule_arithmetic_338 data_program,
    ok_rule_arithmetic_339 data_program,
    ok_rule_arithmetic_340 data_program,
    ok_rule_arithmetic_346 data_program,
    ok_rule_arithmetic_352 data_program,
    ok_rule_arithmetic_353 data_program,
    ok_rule_arithmetic_354 data_program,
    ok_rule_arithmetic_355 data_program,
    ok_rule_arithmetic_356 data_program,
    ok_rule_arithmetic_357 data_program,
    ok_rule_arithmetic_358 data_program,
    ok_rule_arithmetic_359 data_program,
    ok_rule_arithmetic_362 data_program,
    ok_rule_arithmetic_363 data_program,
    ok_rule_arithmetic_364 data_program,
    ok_rule_arithmetic_365 data_program,
    ok_rule_arithmetic_366 data_program,
    ok_rule_arithmetic_367 data_program,
    ok_rule_arithmetic_368 data_program,
    ok_rule_arithmetic_369 data_program,
    ok_rule_arithmetic_372 data_program,
    ok_rule_arithmetic_373 data_program,
    ok_rule_arithmetic_374 data_program,
    ok_rule_arithmetic_375 data_program,
    ok_rule_arithmetic_378 data_program,
    ok_rule_arithmetic_379 data_program,
    ok_rule_arithmetic_380 data_program,
    ok_rule_arithmetic_381 data_program,
    ok_rule_arithmetic_384 data_program,
    ok_rule_arithmetic_385 data_program,
    ok_rule_arithmetic_388 data_program,
    ok_rule_arithmetic_389 data_program,
    ok_rule_arithmetic_390 data_program,
    ok_rule_arithmetic_391 data_program,
    ok_rule_arithmetic_424 data_program,
    ok_rule_arithmetic_451 data_program,
    ok_rule_arithmetic_452 data_program,
    ok_rule_arithmetic_453 data_program,
    ok_rule_arithmetic_454 data_program,
    ok_rule_arithmetic_457 data_program,
    ok_rule_arithmetic_458 data_program,
    ok_rule_arithmetic_459 data_program,
    ok_rule_arithmetic_460 data_program,
    ok_rule_arithmetic_461 data_program,
    ok_rule_arithmetic_462 data_program,
    ok_rule_arithmetic_463 data_program,
    ok_rule_arithmetic_464 data_program,
    ok_rule_arithmetic_467 data_program,
    ok_rule_arithmetic_468 data_program,
    ok_rule_arithmetic_469 data_program,
    ok_rule_arithmetic_470 data_program,
    ok_rule_arithmetic_471 data_program,
    ok_rule_arithmetic_472 data_program,
    ok_rule_arithmetic_473 data_program,
    ok_rule_arithmetic_474 data_program,
    ok_rule_arithmetic_477 data_program,
    ok_rule_arithmetic_478 data_program,
    ok_rule_arithmetic_479 data_program,
    ok_rule_arithmetic_480 data_program,
    ok_rule_arithmetic_481 data_program,
    ok_rule_arithmetic_482 data_program,
    ok_rule_arithmetic_483 data_program,
    ok_rule_arithmetic_484 data_program,
    ok_rule_arithmetic_485 data_program,
    ok_rule_arithmetic_486 data_program,
    ok_rule_arithmetic_487 data_program,
    ok_rule_arithmetic_488 data_program,
    ok_rule_arithmetic_489 data_program,
    ok_rule_arithmetic_490 data_program,
    ok_rule_arithmetic_491 data_program,
    ok_rule_arithmetic_492 data_program,
    ok_rule_arithmetic_495 data_program,
    ok_rule_arithmetic_496 data_program,
    ok_rule_arithmetic_497 data_program,
    ok_rule_arithmetic_498 data_program,
    ok_rule_arithmetic_500 data_program,
    ok_rule_arithmetic_501 data_program,
    ok_rule_arithmetic_502 data_program,
    ok_rule_arithmetic_503 data_program,
    ok_rule_arithmetic_505 data_program,
    ok_rule_arithmetic_506 data_program,
    ok_rule_arithmetic_507 data_program,
    ok_rule_arithmetic_508 data_program,
    ok_rule_arithmetic_510 data_program,
    ok_rule_arithmetic_511 data_program,
    ok_rule_arithmetic_512 data_program,
    ok_rule_arithmetic_513 data_program,
    ok_rule_arithmetic_515 data_program,
    ok_rule_arithmetic_516 data_program,
    ok_rule_arithmetic_517 data_program,
    ok_rule_arithmetic_518 data_program,
    ok_rule_arithmetic_520 data_program,
    ok_rule_arithmetic_521 data_program,
    ok_rule_arithmetic_522 data_program,
    ok_rule_arithmetic_523 data_program,
    ok_rule_arithmetic_525 data_program,
    ok_rule_arithmetic_526 data_program,
    ok_rule_arithmetic_527 data_program,
    ok_rule_arithmetic_528 data_program,
    ok_rule_arithmetic_530 data_program,
    ok_rule_arithmetic_531 data_program,
    ok_rule_arithmetic_532 data_program,
    ok_rule_arithmetic_533 data_program,
    ok_rule_arithmetic_536 data_program,
    ok_rule_arithmetic_537 data_program,
    ok_rule_arithmetic_538 data_program,
    ok_rule_arithmetic_539 data_program,
    ok_rule_arithmetic_541 data_program,
    ok_rule_arithmetic_542 data_program,
    ok_rule_arithmetic_543 data_program,
    ok_rule_arithmetic_544 data_program,
    ok_rule_arithmetic_546 data_program,
    ok_rule_arithmetic_547 data_program,
    ok_rule_arithmetic_548 data_program,
    ok_rule_arithmetic_549 data_program,
    ok_rule_arithmetic_551 data_program,
    ok_rule_arithmetic_552 data_program,
    ok_rule_arithmetic_553 data_program,
    ok_rule_arithmetic_554 data_program,
    ok_rule_arithmetic_556 data_program,
    ok_rule_arithmetic_557 data_program,
    ok_rule_arithmetic_558 data_program,
    ok_rule_arithmetic_559 data_program,
    ok_rule_arithmetic_561 data_program,
    ok_rule_arithmetic_562 data_program,
    ok_rule_arithmetic_563 data_program,
    ok_rule_arithmetic_564 data_program,
    ok_rule_arithmetic_566 data_program,
    ok_rule_arithmetic_567 data_program,
    ok_rule_arithmetic_568 data_program,
    ok_rule_arithmetic_569 data_program,
    ok_rule_arithmetic_571 data_program,
    ok_rule_arithmetic_572 data_program,
    ok_rule_arithmetic_573 data_program,
    ok_rule_arithmetic_574 data_program,
    ok_rule_arithmetic_599 data_program,
    ok_rule_cprop_3 data_program,
    ok_rule_cprop_9 data_program,
    ok_rule_cprop_14 data_program,
    ok_rule_cprop_20 data_program,
    ok_rule_cprop_26 data_program,
    ok_rule_cprop_56 data_program,
    ok_rule_cprop_62 data_program,
    ok_rule_cprop_68 data_program,
    ok_rule_cprop_74 data_program,
    ok_rule_cprop_104 data_program,
    ok_rule_cprop_109 data_program,
    ok_rule_cprop_114 data_program,
    ok_rule_cprop_119 data_program,
    ok_rule_cprop_147 data_program,
    ok_rule_cprop_152 data_program,
    ok_rule_cprop_155 data_program,
    ok_rule_cprop_159 data_program,
    ok_rule_cprop_162 data_program,
    ok_rule_cprop_165 data_program,
    ok_rule_cprop_169 data_program,
    ok_rule_cprop_170 data_program,
    ok_rule_cprop_171 data_program,
    ok_rule_cprop_172 data_program,
    ok_rule_cprop_174 data_program,
    ok_rule_cprop_183 data_program,
    ok_rule_cprop_193 data_program,
    ok_rule_cprop_197 data_program,
    ok_rule_cprop_201 data_program,
    ok_rule_cprop_205 data_program,
    ok_rule_cprop_209 data_program,
    ok_rule_cprop_214 data_program,
    ok_rule_cprop_217 data_program,
    ok_rule_cprop_220 data_program,
    ok_rule_cprop_223 data_program,
    ok_rule_cprop_227 data_program,
    ok_rule_cprop_229 data_program,
    ok_rule_cprop_232 data_program,
    ok_rule_cprop_235 data_program,
    ok_rule_cprop_238 data_program,
    ok_rule_cprop_241 data_program,
    ok_rule_cprop_247 data_program,
    ok_rule_cprop_249 data_program,
    ok_rule_cprop_252 data_program,
    ok_rule_cprop_254 data_program,
    ok_rule_cprop_257 data_program,
    ok_rule_cprop_259 data_program,
    ok_rule_cprop_333 data_program,
    ok_rule_cprop_337 data_program,
    ok_rule_cprop_341 data_program,
    ok_rule_cprop_345 data_program,
    ok_rule_cprop_349 data_program,
    ok_rule_cprop_521 data_program,
    trivial⟩

set_option maxRecDepth 20000 in
theorem simplifyRulesCorrect_proven : SimplifyRulesCorrect program RuleAllow.proven.pred := by
  intro r hr ha
  have hm : r ∈ (program.rulesOf T.«simplify».id).filter (fun r => RuleAllow.proven.pred r.id) :=
    List.mem_filter.2 ⟨hr, ha⟩
  have hall := proven_rules_ok
  generalize (program.rulesOf T.«simplify».id).filter (fun r => RuleAllow.proven.pred r.id) = rs
    at hm hall
  exact AllOk.mem hall r hm

/-- **The proven rule set is sound.** -/
theorem simplifySound_proven : SimplifySound (RuleSetId.fnWith .proven .cranelift) :=
  simplifySound _ simplifyRulesCorrect_proven (by rw [simplify_rules_length]; decide)

set_option maxRecDepth 20000 in
/-- No `simplify_skeleton` rule is in the proven allow-list. -/
theorem skeleton_rules_proven :
    (program.rulesOf T.«simplify_skeleton».id).filter (fun r => RuleAllow.proven.pred r.id) = [] := by
  rfl

set_option maxRecDepth 20000 in
theorem skeleton_rules_length : (program.rulesOf T.«simplify_skeleton».id).length = 39 := by
  rfl

theorem skeletonRulesCorrect_proven : SkeletonRulesCorrect program RuleAllow.proven.pred := by
  intro r hr ha
  have hm : r ∈ (program.rulesOf T.«simplify_skeleton».id).filter
      (fun r => RuleAllow.proven.pred r.id) := List.mem_filter.2 ⟨hr, ha⟩
  rw [skeleton_rules_proven] at hm
  cases hm

/-- **The proven skeleton rule set is sound** (the obligation `simplify`'s pass proof takes for
`Opt.Config.skeletonFn` with `ruleAllow := .proven`). -/
theorem skeletonSound_proven : SkeletonSound (RuleSetId.skeletonFnWith .proven .cranelift) :=
  skeletonSound _ skeletonRulesCorrect_proven (by rw [skeleton_rules_length]; decide)

end Opt.Proof
