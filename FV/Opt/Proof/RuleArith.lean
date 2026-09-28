import FV.Opt.Proof.RuleAuto

/-!
# `opts/arithmetic.isle`: proven `simplify` rules

Each theorem is the batching template `rule_auto` (`FV/Opt/Proof/RuleAuto.lean`) on the rule's
data, for an abstract program with `Data p`; the types `i8`..`i128` are all covered where the rule
applies. The 86 other `simplify` roots of the file are not proven yet (see `docs/contracts/midend.md`,
"Rule proofs": if-lets and internal constructors with if-lets (`iconst_u`/`iconst_s` on the right),
`imm64_power_of_two`, multiplication identities beyond `bv_decide`'s reach, `iabs`; lines 616-622
pass alone but hit the 10 s SAT timeout under a full parallel build, so they are left out).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `arithmetic.isle:8`. -/
theorem ok_rule_arithmetic_8 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_8 := by
  rule_auto rule_arithmetic_8

/-- `arithmetic.isle:13`. -/
theorem ok_rule_arithmetic_13 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_13 := by
  rule_auto rule_arithmetic_13

/-- `arithmetic.isle:18`. -/
theorem ok_rule_arithmetic_18 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_18 := by
  rule_auto rule_arithmetic_18

/-- `arithmetic.isle:24`. -/
theorem ok_rule_arithmetic_24 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_24 := by
  rule_auto rule_arithmetic_24

/-- `arithmetic.isle:26`. -/
theorem ok_rule_arithmetic_26 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_26 := by
  rule_auto rule_arithmetic_26

/-- `arithmetic.isle:28`. -/
theorem ok_rule_arithmetic_28 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_28 := by
  rule_auto rule_arithmetic_28

/-- `arithmetic.isle:31`. -/
theorem ok_rule_arithmetic_31 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_31 := by
  rule_auto rule_arithmetic_31

/-- `arithmetic.isle:35`. -/
theorem ok_rule_arithmetic_35 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_35 := by
  rule_auto rule_arithmetic_35

/-- `arithmetic.isle:59`. -/
theorem ok_rule_arithmetic_59 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_59 := by
  rule_auto rule_arithmetic_59

/-- `arithmetic.isle:233`. -/
theorem ok_rule_arithmetic_233 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_233 := by
  rule_auto rule_arithmetic_233

/-- `arithmetic.isle:239`. -/
theorem ok_rule_arithmetic_239 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_239 := by
  rule_auto rule_arithmetic_239

/-- `arithmetic.isle:240`. -/
theorem ok_rule_arithmetic_240 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_240 := by
  rule_auto rule_arithmetic_240

/-- `arithmetic.isle:243`. -/
theorem ok_rule_arithmetic_243 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_243 := by
  rule_auto rule_arithmetic_243

/-- `arithmetic.isle:244`. -/
theorem ok_rule_arithmetic_244 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_244 := by
  rule_auto rule_arithmetic_244

/-- `arithmetic.isle:247`. -/
theorem ok_rule_arithmetic_247 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_247 := by
  rule_auto rule_arithmetic_247

/-- `arithmetic.isle:295`. -/
theorem ok_rule_arithmetic_295 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_295 := by
  rule_auto rule_arithmetic_295

/-- `arithmetic.isle:296`. -/
theorem ok_rule_arithmetic_296 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_296 := by
  rule_auto rule_arithmetic_296

/-- `arithmetic.isle:297`. -/
theorem ok_rule_arithmetic_297 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_297 := by
  rule_auto rule_arithmetic_297

/-- `arithmetic.isle:298`. -/
theorem ok_rule_arithmetic_298 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_298 := by
  rule_auto rule_arithmetic_298

/-- `arithmetic.isle:301`. -/
theorem ok_rule_arithmetic_301 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_301 := by
  rule_auto rule_arithmetic_301

/-- `arithmetic.isle:302`. -/
theorem ok_rule_arithmetic_302 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_302 := by
  rule_auto rule_arithmetic_302

/-- `arithmetic.isle:303`. -/
theorem ok_rule_arithmetic_303 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_303 := by
  rule_auto rule_arithmetic_303

/-- `arithmetic.isle:304`. -/
theorem ok_rule_arithmetic_304 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_304 := by
  rule_auto rule_arithmetic_304

/-- `arithmetic.isle:307`. -/
theorem ok_rule_arithmetic_307 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_307 := by
  rule_auto rule_arithmetic_307

/-- `arithmetic.isle:308`. -/
theorem ok_rule_arithmetic_308 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_308 := by
  rule_auto rule_arithmetic_308

/-- `arithmetic.isle:311`. -/
theorem ok_rule_arithmetic_311 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_311 := by
  rule_auto rule_arithmetic_311

/-- `arithmetic.isle:312`. -/
theorem ok_rule_arithmetic_312 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_312 := by
  rule_auto rule_arithmetic_312

/-- `arithmetic.isle:313`. -/
theorem ok_rule_arithmetic_313 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_313 := by
  rule_auto rule_arithmetic_313

/-- `arithmetic.isle:314`. -/
theorem ok_rule_arithmetic_314 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_314 := by
  rule_auto rule_arithmetic_314

/-- `arithmetic.isle:317`. -/
theorem ok_rule_arithmetic_317 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_317 := by
  rule_auto rule_arithmetic_317

/-- `arithmetic.isle:318`. -/
theorem ok_rule_arithmetic_318 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_318 := by
  rule_auto rule_arithmetic_318

/-- `arithmetic.isle:319`. -/
theorem ok_rule_arithmetic_319 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_319 := by
  rule_auto rule_arithmetic_319

/-- `arithmetic.isle:320`. -/
theorem ok_rule_arithmetic_320 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_320 := by
  rule_auto rule_arithmetic_320

/-- `arithmetic.isle:323`. -/
theorem ok_rule_arithmetic_323 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_323 := by
  rule_auto rule_arithmetic_323

/-- `arithmetic.isle:324`. -/
theorem ok_rule_arithmetic_324 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_324 := by
  rule_auto rule_arithmetic_324

/-- `arithmetic.isle:337`. -/
theorem ok_rule_arithmetic_337 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_337 := by
  rule_auto rule_arithmetic_337

/-- `arithmetic.isle:338`. -/
theorem ok_rule_arithmetic_338 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_338 := by
  rule_auto rule_arithmetic_338

/-- `arithmetic.isle:339`. -/
theorem ok_rule_arithmetic_339 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_339 := by
  rule_auto rule_arithmetic_339

/-- `arithmetic.isle:340`. -/
theorem ok_rule_arithmetic_340 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_340 := by
  rule_auto rule_arithmetic_340

/-- `arithmetic.isle:346`. -/
theorem ok_rule_arithmetic_346 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_346 := by
  rule_auto rule_arithmetic_346

/-- `arithmetic.isle:352`. -/
theorem ok_rule_arithmetic_352 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_352 := by
  rule_auto rule_arithmetic_352

/-- `arithmetic.isle:353`. -/
theorem ok_rule_arithmetic_353 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_353 := by
  rule_auto rule_arithmetic_353

/-- `arithmetic.isle:354`. -/
theorem ok_rule_arithmetic_354 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_354 := by
  rule_auto rule_arithmetic_354

/-- `arithmetic.isle:355`. -/
theorem ok_rule_arithmetic_355 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_355 := by
  rule_auto rule_arithmetic_355

/-- `arithmetic.isle:356`. -/
theorem ok_rule_arithmetic_356 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_356 := by
  rule_auto rule_arithmetic_356

/-- `arithmetic.isle:357`. -/
theorem ok_rule_arithmetic_357 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_357 := by
  rule_auto rule_arithmetic_357

/-- `arithmetic.isle:358`. -/
theorem ok_rule_arithmetic_358 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_358 := by
  rule_auto rule_arithmetic_358

/-- `arithmetic.isle:359`. -/
theorem ok_rule_arithmetic_359 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_359 := by
  rule_auto rule_arithmetic_359

/-- `arithmetic.isle:362`. -/
theorem ok_rule_arithmetic_362 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_362 := by
  rule_auto rule_arithmetic_362

/-- `arithmetic.isle:363`. -/
theorem ok_rule_arithmetic_363 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_363 := by
  rule_auto rule_arithmetic_363

/-- `arithmetic.isle:364`. -/
theorem ok_rule_arithmetic_364 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_364 := by
  rule_auto rule_arithmetic_364

/-- `arithmetic.isle:365`. -/
theorem ok_rule_arithmetic_365 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_365 := by
  rule_auto rule_arithmetic_365

/-- `arithmetic.isle:366`. -/
theorem ok_rule_arithmetic_366 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_366 := by
  rule_auto rule_arithmetic_366

/-- `arithmetic.isle:367`. -/
theorem ok_rule_arithmetic_367 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_367 := by
  rule_auto rule_arithmetic_367

/-- `arithmetic.isle:368`. -/
theorem ok_rule_arithmetic_368 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_368 := by
  rule_auto rule_arithmetic_368

/-- `arithmetic.isle:369`. -/
theorem ok_rule_arithmetic_369 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_369 := by
  rule_auto rule_arithmetic_369

/-- `arithmetic.isle:372`. -/
theorem ok_rule_arithmetic_372 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_372 := by
  rule_auto rule_arithmetic_372

/-- `arithmetic.isle:373`. -/
theorem ok_rule_arithmetic_373 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_373 := by
  rule_auto rule_arithmetic_373

/-- `arithmetic.isle:374`. -/
theorem ok_rule_arithmetic_374 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_374 := by
  rule_auto rule_arithmetic_374

/-- `arithmetic.isle:375`. -/
theorem ok_rule_arithmetic_375 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_375 := by
  rule_auto rule_arithmetic_375

/-- `arithmetic.isle:378`. -/
theorem ok_rule_arithmetic_378 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_378 := by
  rule_auto rule_arithmetic_378

/-- `arithmetic.isle:379`. -/
theorem ok_rule_arithmetic_379 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_379 := by
  rule_auto rule_arithmetic_379

/-- `arithmetic.isle:380`. -/
theorem ok_rule_arithmetic_380 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_380 := by
  rule_auto rule_arithmetic_380

/-- `arithmetic.isle:381`. -/
theorem ok_rule_arithmetic_381 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_381 := by
  rule_auto rule_arithmetic_381

/-- `arithmetic.isle:384`. -/
theorem ok_rule_arithmetic_384 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_384 := by
  rule_auto rule_arithmetic_384

/-- `arithmetic.isle:385`. -/
theorem ok_rule_arithmetic_385 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_385 := by
  rule_auto rule_arithmetic_385

/-- `arithmetic.isle:388`. -/
theorem ok_rule_arithmetic_388 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_388 := by
  rule_auto rule_arithmetic_388

/-- `arithmetic.isle:389`. -/
theorem ok_rule_arithmetic_389 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_389 := by
  rule_auto rule_arithmetic_389

/-- `arithmetic.isle:390`. -/
theorem ok_rule_arithmetic_390 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_390 := by
  rule_auto rule_arithmetic_390

/-- `arithmetic.isle:391`. -/
theorem ok_rule_arithmetic_391 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_391 := by
  rule_auto rule_arithmetic_391

/-- `arithmetic.isle:424`. -/
theorem ok_rule_arithmetic_424 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_424 := by
  rule_auto rule_arithmetic_424

/-- `arithmetic.isle:451`. -/
theorem ok_rule_arithmetic_451 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_451 := by
  rule_auto rule_arithmetic_451

/-- `arithmetic.isle:452`. -/
theorem ok_rule_arithmetic_452 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_452 := by
  rule_auto rule_arithmetic_452

/-- `arithmetic.isle:453`. -/
theorem ok_rule_arithmetic_453 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_453 := by
  rule_auto rule_arithmetic_453

/-- `arithmetic.isle:454`. -/
theorem ok_rule_arithmetic_454 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_454 := by
  rule_auto rule_arithmetic_454

/-- `arithmetic.isle:457`. -/
theorem ok_rule_arithmetic_457 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_457 := by
  rule_auto rule_arithmetic_457

/-- `arithmetic.isle:458`. -/
theorem ok_rule_arithmetic_458 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_458 := by
  rule_auto rule_arithmetic_458

/-- `arithmetic.isle:459`. -/
theorem ok_rule_arithmetic_459 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_459 := by
  rule_auto rule_arithmetic_459

/-- `arithmetic.isle:460`. -/
theorem ok_rule_arithmetic_460 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_460 := by
  rule_auto rule_arithmetic_460

/-- `arithmetic.isle:461`. -/
theorem ok_rule_arithmetic_461 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_461 := by
  rule_auto rule_arithmetic_461

/-- `arithmetic.isle:462`. -/
theorem ok_rule_arithmetic_462 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_462 := by
  rule_auto rule_arithmetic_462

/-- `arithmetic.isle:463`. -/
theorem ok_rule_arithmetic_463 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_463 := by
  rule_auto rule_arithmetic_463

/-- `arithmetic.isle:464`. -/
theorem ok_rule_arithmetic_464 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_464 := by
  rule_auto rule_arithmetic_464

/-- `arithmetic.isle:467`. -/
theorem ok_rule_arithmetic_467 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_467 := by
  rule_auto rule_arithmetic_467

/-- `arithmetic.isle:468`. -/
theorem ok_rule_arithmetic_468 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_468 := by
  rule_auto rule_arithmetic_468

/-- `arithmetic.isle:469`. -/
theorem ok_rule_arithmetic_469 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_469 := by
  rule_auto rule_arithmetic_469

/-- `arithmetic.isle:470`. -/
theorem ok_rule_arithmetic_470 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_470 := by
  rule_auto rule_arithmetic_470

/-- `arithmetic.isle:471`. -/
theorem ok_rule_arithmetic_471 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_471 := by
  rule_auto rule_arithmetic_471

/-- `arithmetic.isle:472`. -/
theorem ok_rule_arithmetic_472 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_472 := by
  rule_auto rule_arithmetic_472

/-- `arithmetic.isle:473`. -/
theorem ok_rule_arithmetic_473 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_473 := by
  rule_auto rule_arithmetic_473

/-- `arithmetic.isle:474`. -/
theorem ok_rule_arithmetic_474 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_474 := by
  rule_auto rule_arithmetic_474

/-- `arithmetic.isle:477`. -/
theorem ok_rule_arithmetic_477 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_477 := by
  rule_auto rule_arithmetic_477

/-- `arithmetic.isle:478`. -/
theorem ok_rule_arithmetic_478 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_478 := by
  rule_auto rule_arithmetic_478

/-- `arithmetic.isle:479`. -/
theorem ok_rule_arithmetic_479 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_479 := by
  rule_auto rule_arithmetic_479

/-- `arithmetic.isle:480`. -/
theorem ok_rule_arithmetic_480 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_480 := by
  rule_auto rule_arithmetic_480

/-- `arithmetic.isle:481`. -/
theorem ok_rule_arithmetic_481 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_481 := by
  rule_auto rule_arithmetic_481

/-- `arithmetic.isle:482`. -/
theorem ok_rule_arithmetic_482 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_482 := by
  rule_auto rule_arithmetic_482

/-- `arithmetic.isle:483`. -/
theorem ok_rule_arithmetic_483 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_483 := by
  rule_auto rule_arithmetic_483

/-- `arithmetic.isle:484`. -/
theorem ok_rule_arithmetic_484 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_484 := by
  rule_auto rule_arithmetic_484

/-- `arithmetic.isle:485`. -/
theorem ok_rule_arithmetic_485 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_485 := by
  rule_auto rule_arithmetic_485

/-- `arithmetic.isle:486`. -/
theorem ok_rule_arithmetic_486 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_486 := by
  rule_auto rule_arithmetic_486

/-- `arithmetic.isle:487`. -/
theorem ok_rule_arithmetic_487 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_487 := by
  rule_auto rule_arithmetic_487

/-- `arithmetic.isle:488`. -/
theorem ok_rule_arithmetic_488 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_488 := by
  rule_auto rule_arithmetic_488

/-- `arithmetic.isle:489`. -/
theorem ok_rule_arithmetic_489 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_489 := by
  rule_auto rule_arithmetic_489

/-- `arithmetic.isle:490`. -/
theorem ok_rule_arithmetic_490 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_490 := by
  rule_auto rule_arithmetic_490

/-- `arithmetic.isle:491`. -/
theorem ok_rule_arithmetic_491 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_491 := by
  rule_auto rule_arithmetic_491

/-- `arithmetic.isle:492`. -/
theorem ok_rule_arithmetic_492 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_492 := by
  rule_auto rule_arithmetic_492

/-- `arithmetic.isle:495`. -/
theorem ok_rule_arithmetic_495 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_495 := by
  rule_auto rule_arithmetic_495

/-- `arithmetic.isle:496`. -/
theorem ok_rule_arithmetic_496 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_496 := by
  rule_auto rule_arithmetic_496

/-- `arithmetic.isle:497`. -/
theorem ok_rule_arithmetic_497 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_497 := by
  rule_auto rule_arithmetic_497

/-- `arithmetic.isle:498`. -/
theorem ok_rule_arithmetic_498 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_498 := by
  rule_auto rule_arithmetic_498

/-- `arithmetic.isle:500`. -/
theorem ok_rule_arithmetic_500 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_500 := by
  rule_auto rule_arithmetic_500

/-- `arithmetic.isle:501`. -/
theorem ok_rule_arithmetic_501 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_501 := by
  rule_auto rule_arithmetic_501

/-- `arithmetic.isle:502`. -/
theorem ok_rule_arithmetic_502 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_502 := by
  rule_auto rule_arithmetic_502

/-- `arithmetic.isle:503`. -/
theorem ok_rule_arithmetic_503 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_503 := by
  rule_auto rule_arithmetic_503

/-- `arithmetic.isle:505`. -/
theorem ok_rule_arithmetic_505 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_505 := by
  rule_auto rule_arithmetic_505

/-- `arithmetic.isle:506`. -/
theorem ok_rule_arithmetic_506 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_506 := by
  rule_auto rule_arithmetic_506

/-- `arithmetic.isle:507`. -/
theorem ok_rule_arithmetic_507 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_507 := by
  rule_auto rule_arithmetic_507

/-- `arithmetic.isle:508`. -/
theorem ok_rule_arithmetic_508 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_508 := by
  rule_auto rule_arithmetic_508

/-- `arithmetic.isle:510`. -/
theorem ok_rule_arithmetic_510 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_510 := by
  rule_auto rule_arithmetic_510

/-- `arithmetic.isle:511`. -/
theorem ok_rule_arithmetic_511 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_511 := by
  rule_auto rule_arithmetic_511

/-- `arithmetic.isle:512`. -/
theorem ok_rule_arithmetic_512 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_512 := by
  rule_auto rule_arithmetic_512

/-- `arithmetic.isle:513`. -/
theorem ok_rule_arithmetic_513 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_513 := by
  rule_auto rule_arithmetic_513

/-- `arithmetic.isle:515`. -/
theorem ok_rule_arithmetic_515 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_515 := by
  rule_auto rule_arithmetic_515

/-- `arithmetic.isle:516`. -/
theorem ok_rule_arithmetic_516 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_516 := by
  rule_auto rule_arithmetic_516

/-- `arithmetic.isle:517`. -/
theorem ok_rule_arithmetic_517 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_517 := by
  rule_auto rule_arithmetic_517

/-- `arithmetic.isle:518`. -/
theorem ok_rule_arithmetic_518 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_518 := by
  rule_auto rule_arithmetic_518

/-- `arithmetic.isle:520`. -/
theorem ok_rule_arithmetic_520 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_520 := by
  rule_auto rule_arithmetic_520

/-- `arithmetic.isle:521`. -/
theorem ok_rule_arithmetic_521 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_521 := by
  rule_auto rule_arithmetic_521

/-- `arithmetic.isle:522`. -/
theorem ok_rule_arithmetic_522 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_522 := by
  rule_auto rule_arithmetic_522

/-- `arithmetic.isle:523`. -/
theorem ok_rule_arithmetic_523 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_523 := by
  rule_auto rule_arithmetic_523

/-- `arithmetic.isle:525`. -/
theorem ok_rule_arithmetic_525 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_525 := by
  rule_auto rule_arithmetic_525

/-- `arithmetic.isle:526`. -/
theorem ok_rule_arithmetic_526 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_526 := by
  rule_auto rule_arithmetic_526

/-- `arithmetic.isle:527`. -/
theorem ok_rule_arithmetic_527 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_527 := by
  rule_auto rule_arithmetic_527

/-- `arithmetic.isle:528`. -/
theorem ok_rule_arithmetic_528 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_528 := by
  rule_auto rule_arithmetic_528

/-- `arithmetic.isle:530`. -/
theorem ok_rule_arithmetic_530 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_530 := by
  rule_auto rule_arithmetic_530

/-- `arithmetic.isle:531`. -/
theorem ok_rule_arithmetic_531 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_531 := by
  rule_auto rule_arithmetic_531

/-- `arithmetic.isle:532`. -/
theorem ok_rule_arithmetic_532 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_532 := by
  rule_auto rule_arithmetic_532

/-- `arithmetic.isle:533`. -/
theorem ok_rule_arithmetic_533 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_533 := by
  rule_auto rule_arithmetic_533

/-- `arithmetic.isle:536`. -/
theorem ok_rule_arithmetic_536 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_536 := by
  rule_auto rule_arithmetic_536

/-- `arithmetic.isle:537`. -/
theorem ok_rule_arithmetic_537 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_537 := by
  rule_auto rule_arithmetic_537

/-- `arithmetic.isle:538`. -/
theorem ok_rule_arithmetic_538 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_538 := by
  rule_auto rule_arithmetic_538

/-- `arithmetic.isle:539`. -/
theorem ok_rule_arithmetic_539 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_539 := by
  rule_auto rule_arithmetic_539

/-- `arithmetic.isle:541`. -/
theorem ok_rule_arithmetic_541 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_541 := by
  rule_auto rule_arithmetic_541

/-- `arithmetic.isle:542`. -/
theorem ok_rule_arithmetic_542 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_542 := by
  rule_auto rule_arithmetic_542

/-- `arithmetic.isle:543`. -/
theorem ok_rule_arithmetic_543 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_543 := by
  rule_auto rule_arithmetic_543

/-- `arithmetic.isle:544`. -/
theorem ok_rule_arithmetic_544 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_544 := by
  rule_auto rule_arithmetic_544

/-- `arithmetic.isle:546`. -/
theorem ok_rule_arithmetic_546 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_546 := by
  rule_auto rule_arithmetic_546

/-- `arithmetic.isle:547`. -/
theorem ok_rule_arithmetic_547 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_547 := by
  rule_auto rule_arithmetic_547

/-- `arithmetic.isle:548`. -/
theorem ok_rule_arithmetic_548 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_548 := by
  rule_auto rule_arithmetic_548

/-- `arithmetic.isle:549`. -/
theorem ok_rule_arithmetic_549 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_549 := by
  rule_auto rule_arithmetic_549

/-- `arithmetic.isle:551`. -/
theorem ok_rule_arithmetic_551 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_551 := by
  rule_auto rule_arithmetic_551

/-- `arithmetic.isle:552`. -/
theorem ok_rule_arithmetic_552 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_552 := by
  rule_auto rule_arithmetic_552

/-- `arithmetic.isle:553`. -/
theorem ok_rule_arithmetic_553 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_553 := by
  rule_auto rule_arithmetic_553

/-- `arithmetic.isle:554`. -/
theorem ok_rule_arithmetic_554 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_554 := by
  rule_auto rule_arithmetic_554

/-- `arithmetic.isle:556`. -/
theorem ok_rule_arithmetic_556 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_556 := by
  rule_auto rule_arithmetic_556

/-- `arithmetic.isle:557`. -/
theorem ok_rule_arithmetic_557 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_557 := by
  rule_auto rule_arithmetic_557

/-- `arithmetic.isle:558`. -/
theorem ok_rule_arithmetic_558 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_558 := by
  rule_auto rule_arithmetic_558

/-- `arithmetic.isle:559`. -/
theorem ok_rule_arithmetic_559 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_559 := by
  rule_auto rule_arithmetic_559

/-- `arithmetic.isle:561`. -/
theorem ok_rule_arithmetic_561 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_561 := by
  rule_auto rule_arithmetic_561

/-- `arithmetic.isle:562`. -/
theorem ok_rule_arithmetic_562 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_562 := by
  rule_auto rule_arithmetic_562

/-- `arithmetic.isle:563`. -/
theorem ok_rule_arithmetic_563 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_563 := by
  rule_auto rule_arithmetic_563

/-- `arithmetic.isle:564`. -/
theorem ok_rule_arithmetic_564 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_564 := by
  rule_auto rule_arithmetic_564

/-- `arithmetic.isle:566`. -/
theorem ok_rule_arithmetic_566 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_566 := by
  rule_auto rule_arithmetic_566

/-- `arithmetic.isle:567`. -/
theorem ok_rule_arithmetic_567 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_567 := by
  rule_auto rule_arithmetic_567

/-- `arithmetic.isle:568`. -/
theorem ok_rule_arithmetic_568 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_568 := by
  rule_auto rule_arithmetic_568

/-- `arithmetic.isle:569`. -/
theorem ok_rule_arithmetic_569 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_569 := by
  rule_auto rule_arithmetic_569

/-- `arithmetic.isle:571`. -/
theorem ok_rule_arithmetic_571 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_571 := by
  rule_auto rule_arithmetic_571

/-- `arithmetic.isle:572`. -/
theorem ok_rule_arithmetic_572 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_572 := by
  rule_auto rule_arithmetic_572

/-- `arithmetic.isle:573`. -/
theorem ok_rule_arithmetic_573 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_573 := by
  rule_auto rule_arithmetic_573

/-- `arithmetic.isle:574`. -/
theorem ok_rule_arithmetic_574 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_574 := by
  rule_auto rule_arithmetic_574

/-- `arithmetic.isle:599`. -/
theorem ok_rule_arithmetic_599 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_599 := by
  rule_auto rule_arithmetic_599

end Opt.Proof
