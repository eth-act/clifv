import FV.Opt.Proof.RuleAuto

/-!
# `opts/bitops.isle` (part 1): proven `simplify` rules

Each theorem is the batching template `rule_auto` (`FV/Opt/Proof/RuleAuto.lean`) on the rule's
data, for an abstract program with `Data p`. Roots `bitops.isle:21`..`293`; the roots of
this range that are not here are proven in `RuleBitops6.lean`/`RuleBitops7.lean` or listed as not proven in
`docs/contracts/midend.md` ("Rule proofs").
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:23`. -/
theorem ok_rule_bitops_23 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_23 := by
  rule_auto rule_bitops_23

/-- `bitops.isle:40`. -/
theorem ok_rule_bitops_40 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_40 := by
  rule_auto rule_bitops_40

/-- `bitops.isle:53`. -/
theorem ok_rule_bitops_53 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_53 := by
  rule_auto rule_bitops_53

/-- `bitops.isle:56`. -/
theorem ok_rule_bitops_56 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_56 := by
  rule_auto rule_bitops_56

/-- `bitops.isle:59`. -/
theorem ok_rule_bitops_59 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_59 := by
  rule_auto rule_bitops_59

/-- `bitops.isle:68`. -/
theorem ok_rule_bitops_68 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_68 := by
  rule_auto rule_bitops_68

/-- `bitops.isle:104`. -/
theorem ok_rule_bitops_104 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_104 := by
  rule_auto rule_bitops_104

/-- `bitops.isle:199`. -/
theorem ok_rule_bitops_199 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_199 := by
  rule_auto rule_bitops_199

/-- `bitops.isle:202`. -/
theorem ok_rule_bitops_202 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_202 := by
  rule_auto rule_bitops_202

/-- `bitops.isle:203`. -/
theorem ok_rule_bitops_203 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_203 := by
  rule_auto rule_bitops_203

/-- `bitops.isle:204`. -/
theorem ok_rule_bitops_204 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_204 := by
  rule_auto rule_bitops_204

/-- `bitops.isle:205`. -/
theorem ok_rule_bitops_205 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_205 := by
  rule_auto rule_bitops_205

/-- `bitops.isle:207`. -/
theorem ok_rule_bitops_207 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_207 := by
  rule_auto rule_bitops_207

/-- `bitops.isle:208`. -/
theorem ok_rule_bitops_208 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_208 := by
  rule_auto rule_bitops_208

/-- `bitops.isle:209`. -/
theorem ok_rule_bitops_209 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_209 := by
  rule_auto rule_bitops_209

/-- `bitops.isle:210`. -/
theorem ok_rule_bitops_210 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_210 := by
  rule_auto rule_bitops_210

/-- `bitops.isle:213`. -/
theorem ok_rule_bitops_213 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_213 := by
  rule_auto rule_bitops_213

/-- `bitops.isle:214`. -/
theorem ok_rule_bitops_214 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_214 := by
  rule_auto rule_bitops_214

/-- `bitops.isle:215`. -/
theorem ok_rule_bitops_215 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_215 := by
  rule_auto rule_bitops_215

/-- `bitops.isle:216`. -/
theorem ok_rule_bitops_216 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_216 := by
  rule_auto rule_bitops_216

/-- `bitops.isle:219`. -/
theorem ok_rule_bitops_219 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_219 := by
  rule_auto rule_bitops_219

/-- `bitops.isle:220`. -/
theorem ok_rule_bitops_220 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_220 := by
  rule_auto rule_bitops_220

/-- `bitops.isle:223`. -/
theorem ok_rule_bitops_223 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_223 := by
  rule_auto rule_bitops_223

/-- `bitops.isle:224`. -/
theorem ok_rule_bitops_224 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_224 := by
  rule_auto rule_bitops_224

/-- `bitops.isle:227`. -/
theorem ok_rule_bitops_227 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_227 := by
  rule_auto rule_bitops_227

/-- `bitops.isle:228`. -/
theorem ok_rule_bitops_228 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_228 := by
  rule_auto rule_bitops_228

/-- `bitops.isle:231`. -/
theorem ok_rule_bitops_231 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_231 := by
  rule_auto rule_bitops_231

/-- `bitops.isle:232`. -/
theorem ok_rule_bitops_232 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_232 := by
  rule_auto rule_bitops_232

/-- `bitops.isle:235`. -/
theorem ok_rule_bitops_235 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_235 := by
  rule_auto rule_bitops_235

/-- `bitops.isle:236`. -/
theorem ok_rule_bitops_236 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_236 := by
  rule_auto rule_bitops_236

/-- `bitops.isle:239`. -/
theorem ok_rule_bitops_239 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_239 := by
  rule_auto rule_bitops_239

/-- `bitops.isle:244`. -/
theorem ok_rule_bitops_244 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_244 := by
  rule_auto rule_bitops_244

/-- `bitops.isle:245`. -/
theorem ok_rule_bitops_245 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_245 := by
  rule_auto rule_bitops_245

/-- `bitops.isle:246`. -/
theorem ok_rule_bitops_246 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_246 := by
  rule_auto rule_bitops_246

/-- `bitops.isle:247`. -/
theorem ok_rule_bitops_247 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_247 := by
  rule_auto rule_bitops_247

/-- `bitops.isle:248`. -/
theorem ok_rule_bitops_248 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_248 := by
  rule_auto rule_bitops_248

/-- `bitops.isle:249`. -/
theorem ok_rule_bitops_249 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_249 := by
  rule_auto rule_bitops_249

/-- `bitops.isle:250`. -/
theorem ok_rule_bitops_250 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_250 := by
  rule_auto rule_bitops_250

/-- `bitops.isle:251`. -/
theorem ok_rule_bitops_251 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_251 := by
  rule_auto rule_bitops_251

/-- `bitops.isle:254`. -/
theorem ok_rule_bitops_254 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_254 := by
  rule_auto rule_bitops_254

/-- `bitops.isle:256`. -/
theorem ok_rule_bitops_256 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_256 := by
  rule_auto rule_bitops_256

/-- `bitops.isle:258`. -/
theorem ok_rule_bitops_258 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_258 := by
  rule_auto rule_bitops_258

/-- `bitops.isle:260`. -/
theorem ok_rule_bitops_260 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_260 := by
  rule_auto rule_bitops_260

/-- `bitops.isle:264`. -/
theorem ok_rule_bitops_264 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_264 := by
  rule_auto rule_bitops_264

/-- `bitops.isle:265`. -/
theorem ok_rule_bitops_265 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_265 := by
  rule_auto rule_bitops_265

/-- `bitops.isle:266`. -/
theorem ok_rule_bitops_266 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_266 := by
  rule_auto rule_bitops_266

/-- `bitops.isle:267`. -/
theorem ok_rule_bitops_267 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_267 := by
  rule_auto rule_bitops_267

/-- `bitops.isle:270`. -/
theorem ok_rule_bitops_270 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_270 := by
  rule_auto rule_bitops_270

/-- `bitops.isle:271`. -/
theorem ok_rule_bitops_271 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_271 := by
  rule_auto rule_bitops_271

/-- `bitops.isle:272`. -/
theorem ok_rule_bitops_272 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_272 := by
  rule_auto rule_bitops_272

/-- `bitops.isle:273`. -/
theorem ok_rule_bitops_273 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_273 := by
  rule_auto rule_bitops_273

/-- `bitops.isle:274`. -/
theorem ok_rule_bitops_274 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_274 := by
  rule_auto rule_bitops_274

/-- `bitops.isle:275`. -/
theorem ok_rule_bitops_275 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_275 := by
  rule_auto rule_bitops_275

/-- `bitops.isle:276`. -/
theorem ok_rule_bitops_276 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_276 := by
  rule_auto rule_bitops_276

/-- `bitops.isle:277`. -/
theorem ok_rule_bitops_277 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_277 := by
  rule_auto rule_bitops_277

/-- `bitops.isle:280`. -/
theorem ok_rule_bitops_280 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_280 := by
  rule_auto rule_bitops_280

/-- `bitops.isle:281`. -/
theorem ok_rule_bitops_281 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_281 := by
  rule_auto rule_bitops_281

/-- `bitops.isle:282`. -/
theorem ok_rule_bitops_282 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_282 := by
  rule_auto rule_bitops_282

/-- `bitops.isle:283`. -/
theorem ok_rule_bitops_283 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_283 := by
  rule_auto rule_bitops_283

/-- `bitops.isle:284`. -/
theorem ok_rule_bitops_284 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_284 := by
  rule_auto rule_bitops_284

/-- `bitops.isle:285`. -/
theorem ok_rule_bitops_285 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_285 := by
  rule_auto rule_bitops_285

/-- `bitops.isle:286`. -/
theorem ok_rule_bitops_286 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_286 := by
  rule_auto rule_bitops_286

/-- `bitops.isle:287`. -/
theorem ok_rule_bitops_287 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_287 := by
  rule_auto rule_bitops_287

/-- `bitops.isle:290`. -/
theorem ok_rule_bitops_290 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_290 := by
  rule_auto rule_bitops_290

/-- `bitops.isle:291`. -/
theorem ok_rule_bitops_291 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_291 := by
  rule_auto rule_bitops_291

/-- `bitops.isle:292`. -/
theorem ok_rule_bitops_292 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_292 := by
  rule_auto rule_bitops_292

/-- `bitops.isle:293`. -/
theorem ok_rule_bitops_293 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_293 := by
  rule_auto rule_bitops_293

end Opt.Proof
