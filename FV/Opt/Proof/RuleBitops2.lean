import FV.Opt.Proof.RuleAuto

/-!
# `opts/bitops.isle` (part 2): proven `simplify` rules

Each theorem is the batching template `rule_auto` (`FV/Opt/Proof/RuleAuto.lean`) on the rule's
data, for an abstract program with `Data p`. Roots `bitops.isle:294`..`420`; the roots of
this range that are not here are proven in `RuleBitops6.lean`/`RuleBitops7.lean` or listed as not proven in
`docs/contracts/midend.md` ("Rule proofs").
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:294`. -/
theorem ok_rule_bitops_294 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_294 := by
  rule_auto rule_bitops_294

/-- `bitops.isle:295`. -/
theorem ok_rule_bitops_295 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_295 := by
  rule_auto rule_bitops_295

/-- `bitops.isle:296`. -/
theorem ok_rule_bitops_296 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_296 := by
  rule_auto rule_bitops_296

/-- `bitops.isle:297`. -/
theorem ok_rule_bitops_297 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_297 := by
  rule_auto rule_bitops_297

/-- `bitops.isle:300`. -/
theorem ok_rule_bitops_300 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_300 := by
  rule_auto rule_bitops_300

/-- `bitops.isle:301`. -/
theorem ok_rule_bitops_301 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_301 := by
  rule_auto rule_bitops_301

/-- `bitops.isle:304`. -/
theorem ok_rule_bitops_304 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_304 := by
  rule_auto rule_bitops_304

/-- `bitops.isle:305`. -/
theorem ok_rule_bitops_305 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_305 := by
  rule_auto rule_bitops_305

/-- `bitops.isle:308`. -/
theorem ok_rule_bitops_308 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_308 := by
  rule_auto rule_bitops_308

/-- `bitops.isle:309`. -/
theorem ok_rule_bitops_309 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_309 := by
  rule_auto rule_bitops_309

/-- `bitops.isle:310`. -/
theorem ok_rule_bitops_310 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_310 := by
  rule_auto rule_bitops_310

/-- `bitops.isle:311`. -/
theorem ok_rule_bitops_311 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_311 := by
  rule_auto rule_bitops_311

/-- `bitops.isle:312`. -/
theorem ok_rule_bitops_312 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_312 := by
  rule_auto rule_bitops_312

/-- `bitops.isle:313`. -/
theorem ok_rule_bitops_313 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_313 := by
  rule_auto rule_bitops_313

/-- `bitops.isle:314`. -/
theorem ok_rule_bitops_314 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_314 := by
  rule_auto rule_bitops_314

/-- `bitops.isle:315`. -/
theorem ok_rule_bitops_315 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_315 := by
  rule_auto rule_bitops_315

/-- `bitops.isle:318`. -/
theorem ok_rule_bitops_318 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_318 := by
  rule_auto rule_bitops_318

/-- `bitops.isle:319`. -/
theorem ok_rule_bitops_319 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_319 := by
  rule_auto rule_bitops_319

/-- `bitops.isle:320`. -/
theorem ok_rule_bitops_320 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_320 := by
  rule_auto rule_bitops_320

/-- `bitops.isle:321`. -/
theorem ok_rule_bitops_321 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_321 := by
  rule_auto rule_bitops_321

/-- `bitops.isle:322`. -/
theorem ok_rule_bitops_322 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_322 := by
  rule_auto rule_bitops_322

/-- `bitops.isle:323`. -/
theorem ok_rule_bitops_323 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_323 := by
  rule_auto rule_bitops_323

/-- `bitops.isle:324`. -/
theorem ok_rule_bitops_324 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_324 := by
  rule_auto rule_bitops_324

/-- `bitops.isle:325`. -/
theorem ok_rule_bitops_325 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_325 := by
  rule_auto rule_bitops_325

/-- `bitops.isle:328`. -/
theorem ok_rule_bitops_328 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_328 := by
  rule_auto rule_bitops_328

/-- `bitops.isle:329`. -/
theorem ok_rule_bitops_329 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_329 := by
  rule_auto rule_bitops_329

/-- `bitops.isle:330`. -/
theorem ok_rule_bitops_330 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_330 := by
  rule_auto rule_bitops_330

/-- `bitops.isle:331`. -/
theorem ok_rule_bitops_331 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_331 := by
  rule_auto rule_bitops_331

/-- `bitops.isle:334`. -/
theorem ok_rule_bitops_334 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_334 := by
  rule_auto rule_bitops_334

/-- `bitops.isle:335`. -/
theorem ok_rule_bitops_335 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_335 := by
  rule_auto rule_bitops_335

/-- `bitops.isle:336`. -/
theorem ok_rule_bitops_336 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_336 := by
  rule_auto rule_bitops_336

/-- `bitops.isle:337`. -/
theorem ok_rule_bitops_337 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_337 := by
  rule_auto rule_bitops_337

/-- `bitops.isle:340`. -/
theorem ok_rule_bitops_340 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_340 := by
  rule_auto rule_bitops_340

/-- `bitops.isle:341`. -/
theorem ok_rule_bitops_341 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_341 := by
  rule_auto rule_bitops_341

/-- `bitops.isle:342`. -/
theorem ok_rule_bitops_342 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_342 := by
  rule_auto rule_bitops_342

/-- `bitops.isle:343`. -/
theorem ok_rule_bitops_343 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_343 := by
  rule_auto rule_bitops_343

/-- `bitops.isle:346`. -/
theorem ok_rule_bitops_346 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_346 := by
  rule_auto rule_bitops_346

/-- `bitops.isle:347`. -/
theorem ok_rule_bitops_347 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_347 := by
  rule_auto rule_bitops_347

/-- `bitops.isle:348`. -/
theorem ok_rule_bitops_348 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_348 := by
  rule_auto rule_bitops_348

/-- `bitops.isle:349`. -/
theorem ok_rule_bitops_349 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_349 := by
  rule_auto rule_bitops_349

/-- `bitops.isle:350`. -/
theorem ok_rule_bitops_350 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_350 := by
  rule_auto rule_bitops_350

/-- `bitops.isle:351`. -/
theorem ok_rule_bitops_351 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_351 := by
  rule_auto rule_bitops_351

/-- `bitops.isle:352`. -/
theorem ok_rule_bitops_352 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_352 := by
  rule_auto rule_bitops_352

/-- `bitops.isle:353`. -/
theorem ok_rule_bitops_353 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_353 := by
  rule_auto rule_bitops_353

/-- `bitops.isle:356`. -/
theorem ok_rule_bitops_356 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_356 := by
  rule_auto rule_bitops_356

/-- `bitops.isle:357`. -/
theorem ok_rule_bitops_357 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_357 := by
  rule_auto rule_bitops_357

/-- `bitops.isle:358`. -/
theorem ok_rule_bitops_358 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_358 := by
  rule_auto rule_bitops_358

/-- `bitops.isle:359`. -/
theorem ok_rule_bitops_359 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_359 := by
  rule_auto rule_bitops_359

/-- `bitops.isle:360`. -/
theorem ok_rule_bitops_360 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_360 := by
  rule_auto rule_bitops_360

/-- `bitops.isle:361`. -/
theorem ok_rule_bitops_361 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_361 := by
  rule_auto rule_bitops_361

/-- `bitops.isle:362`. -/
theorem ok_rule_bitops_362 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_362 := by
  rule_auto rule_bitops_362

/-- `bitops.isle:363`. -/
theorem ok_rule_bitops_363 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_363 := by
  rule_auto rule_bitops_363

/-- `bitops.isle:366`. -/
theorem ok_rule_bitops_366 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_366 := by
  rule_auto rule_bitops_366

/-- `bitops.isle:367`. -/
theorem ok_rule_bitops_367 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_367 := by
  rule_auto rule_bitops_367

/-- `bitops.isle:370`. -/
theorem ok_rule_bitops_370 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_370 := by
  rule_auto rule_bitops_370

/-- `bitops.isle:371`. -/
theorem ok_rule_bitops_371 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_371 := by
  rule_auto rule_bitops_371

/-- `bitops.isle:374`. -/
theorem ok_rule_bitops_374 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_374 := by
  rule_auto rule_bitops_374

/-- `bitops.isle:375`. -/
theorem ok_rule_bitops_375 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_375 := by
  rule_auto rule_bitops_375

/-- `bitops.isle:376`. -/
theorem ok_rule_bitops_376 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_376 := by
  rule_auto rule_bitops_376

/-- `bitops.isle:377`. -/
theorem ok_rule_bitops_377 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_377 := by
  rule_auto rule_bitops_377

/-- `bitops.isle:380`. -/
theorem ok_rule_bitops_380 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_380 := by
  rule_auto rule_bitops_380

/-- `bitops.isle:381`. -/
theorem ok_rule_bitops_381 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_381 := by
  rule_auto rule_bitops_381

/-- `bitops.isle:382`. -/
theorem ok_rule_bitops_382 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_382 := by
  rule_auto rule_bitops_382

/-- `bitops.isle:383`. -/
theorem ok_rule_bitops_383 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_383 := by
  rule_auto rule_bitops_383

/-- `bitops.isle:386`. -/
theorem ok_rule_bitops_386 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_386 := by
  rule_auto rule_bitops_386

/-- `bitops.isle:387`. -/
theorem ok_rule_bitops_387 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_387 := by
  rule_auto rule_bitops_387

/-- `bitops.isle:388`. -/
theorem ok_rule_bitops_388 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_388 := by
  rule_auto rule_bitops_388

/-- `bitops.isle:389`. -/
theorem ok_rule_bitops_389 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_389 := by
  rule_auto rule_bitops_389

/-- `bitops.isle:392`. -/
theorem ok_rule_bitops_392 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_392 := by
  rule_auto rule_bitops_392

/-- `bitops.isle:393`. -/
theorem ok_rule_bitops_393 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_393 := by
  rule_auto rule_bitops_393

/-- `bitops.isle:394`. -/
theorem ok_rule_bitops_394 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_394 := by
  rule_auto rule_bitops_394

/-- `bitops.isle:395`. -/
theorem ok_rule_bitops_395 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_395 := by
  rule_auto rule_bitops_395

/-- `bitops.isle:398`. -/
theorem ok_rule_bitops_398 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_398 := by
  rule_auto rule_bitops_398

/-- `bitops.isle:399`. -/
theorem ok_rule_bitops_399 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_399 := by
  rule_auto rule_bitops_399

/-- `bitops.isle:401`. -/
theorem ok_rule_bitops_401 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_401 := by
  rule_auto rule_bitops_401

/-- `bitops.isle:403`. -/
theorem ok_rule_bitops_403 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_403 := by
  rule_auto rule_bitops_403

/-- `bitops.isle:404`. -/
theorem ok_rule_bitops_404 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_404 := by
  rule_auto rule_bitops_404

/-- `bitops.isle:406`. -/
theorem ok_rule_bitops_406 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_406 := by
  rule_auto rule_bitops_406

/-- `bitops.isle:408`. -/
theorem ok_rule_bitops_408 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_408 := by
  rule_auto rule_bitops_408

/-- `bitops.isle:409`. -/
theorem ok_rule_bitops_409 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_409 := by
  rule_auto rule_bitops_409

/-- `bitops.isle:411`. -/
theorem ok_rule_bitops_411 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_411 := by
  rule_auto rule_bitops_411

/-- `bitops.isle:413`. -/
theorem ok_rule_bitops_413 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_413 := by
  rule_auto rule_bitops_413

/-- `bitops.isle:414`. -/
theorem ok_rule_bitops_414 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_414 := by
  rule_auto rule_bitops_414

/-- `bitops.isle:416`. -/
theorem ok_rule_bitops_416 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_416 := by
  rule_auto rule_bitops_416

/-- `bitops.isle:419`. -/
theorem ok_rule_bitops_419 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_419 := by
  rule_auto rule_bitops_419

/-- `bitops.isle:420`. -/
theorem ok_rule_bitops_420 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_420 := by
  rule_auto rule_bitops_420

end Opt.Proof
