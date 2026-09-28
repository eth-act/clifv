import FV.Opt.Proof.RuleAuto

/-!
# `opts/cprop.isle`: proven `simplify` rules

Each theorem is the batching template `rule_auto` (`FV/Opt/Proof/RuleAuto.lean`) on the rule's
data, for an abstract program with `Data p`. Constant folds use the helper specifications of
`FV/Opt/Proof/RuleImm.lean` (`opt_imm`). Not yet proven (16 of the 68 roots): the shift/rotate
folds 79-99 (`imm64_sshr`/`rotl`/`rotr` specs missing; `shl`/`ushr` specs are proven), 125, 130,
132, 269 (`iconst_u`/`iconst_s` constructors and `imm64_masked` on the right-hand side: if-lets of
internal constructors), 135 (`imm64_icmp` at a result type differing from the operand type),
320-324 (shift reassociation: amount types), 375-379 (`bswap` folds: `u64_bswap*` specs).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `cprop.isle:3`. -/
theorem ok_rule_cprop_3 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_3 := by
  rule_auto rule_cprop_3

/-- `cprop.isle:9`. -/
theorem ok_rule_cprop_9 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_9 := by
  rule_auto rule_cprop_9

/-- `cprop.isle:14`. -/
theorem ok_rule_cprop_14 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_14 := by
  rule_auto rule_cprop_14

/-- `cprop.isle:20`. -/
theorem ok_rule_cprop_20 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_20 := by
  rule_auto rule_cprop_20

/-- `cprop.isle:26`. -/
theorem ok_rule_cprop_26 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_26 := by
  rule_auto rule_cprop_26

/-- `cprop.isle:56`. -/
theorem ok_rule_cprop_56 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_56 := by
  rule_auto rule_cprop_56

/-- `cprop.isle:62`. -/
theorem ok_rule_cprop_62 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_62 := by
  rule_auto rule_cprop_62

/-- `cprop.isle:68`. -/
theorem ok_rule_cprop_68 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_68 := by
  rule_auto rule_cprop_68

/-- `cprop.isle:74`. -/
theorem ok_rule_cprop_74 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_74 := by
  rule_auto rule_cprop_74

/-- `cprop.isle:104`. -/
theorem ok_rule_cprop_104 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_104 := by
  rule_auto rule_cprop_104

/-- `cprop.isle:109`. -/
theorem ok_rule_cprop_109 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_109 := by
  rule_auto rule_cprop_109

/-- `cprop.isle:114`. -/
theorem ok_rule_cprop_114 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_114 := by
  rule_auto rule_cprop_114

/-- `cprop.isle:119`. -/
theorem ok_rule_cprop_119 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_119 := by
  rule_auto rule_cprop_119

/-- `cprop.isle:147`. -/
theorem ok_rule_cprop_147 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_147 := by
  rule_auto rule_cprop_147

/-- `cprop.isle:152`. -/
theorem ok_rule_cprop_152 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_152 := by
  rule_auto rule_cprop_152

/-- `cprop.isle:155`. -/
theorem ok_rule_cprop_155 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_155 := by
  rule_auto rule_cprop_155

/-- `cprop.isle:159`. -/
theorem ok_rule_cprop_159 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_159 := by
  rule_auto rule_cprop_159

/-- `cprop.isle:162`. -/
theorem ok_rule_cprop_162 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_162 := by
  rule_auto rule_cprop_162

/-- `cprop.isle:165`. -/
theorem ok_rule_cprop_165 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_165 := by
  rule_auto rule_cprop_165

/-- `cprop.isle:169`. -/
theorem ok_rule_cprop_169 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_169 := by
  rule_auto rule_cprop_169

/-- `cprop.isle:170`. -/
theorem ok_rule_cprop_170 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_170 := by
  rule_auto rule_cprop_170

/-- `cprop.isle:171`. -/
theorem ok_rule_cprop_171 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_171 := by
  rule_auto rule_cprop_171

/-- `cprop.isle:172`. -/
theorem ok_rule_cprop_172 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_172 := by
  rule_auto rule_cprop_172

/-- `cprop.isle:174`. -/
theorem ok_rule_cprop_174 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_174 := by
  rule_auto rule_cprop_174

/-- `cprop.isle:183`. -/
theorem ok_rule_cprop_183 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_183 := by
  rule_auto rule_cprop_183

/-- `cprop.isle:193`. -/
theorem ok_rule_cprop_193 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_193 := by
  rule_auto rule_cprop_193

/-- `cprop.isle:197`. -/
theorem ok_rule_cprop_197 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_197 := by
  rule_auto rule_cprop_197

/-- `cprop.isle:201`. -/
theorem ok_rule_cprop_201 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_201 := by
  rule_auto rule_cprop_201

/-- `cprop.isle:205`. -/
theorem ok_rule_cprop_205 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_205 := by
  rule_auto rule_cprop_205

/-- `cprop.isle:209`. -/
theorem ok_rule_cprop_209 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_209 := by
  rule_auto rule_cprop_209

/-- `cprop.isle:214`. -/
theorem ok_rule_cprop_214 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_214 := by
  rule_auto rule_cprop_214

/-- `cprop.isle:217`. -/
theorem ok_rule_cprop_217 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_217 := by
  rule_auto rule_cprop_217

/-- `cprop.isle:220`. -/
theorem ok_rule_cprop_220 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_220 := by
  rule_auto rule_cprop_220

/-- `cprop.isle:223`. -/
theorem ok_rule_cprop_223 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_223 := by
  rule_auto rule_cprop_223

/-- `cprop.isle:227`. -/
theorem ok_rule_cprop_227 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_227 := by
  rule_auto rule_cprop_227

/-- `cprop.isle:229`. -/
theorem ok_rule_cprop_229 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_229 := by
  rule_auto rule_cprop_229

/-- `cprop.isle:232`. -/
theorem ok_rule_cprop_232 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_232 := by
  rule_auto rule_cprop_232

/-- `cprop.isle:235`. -/
theorem ok_rule_cprop_235 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_235 := by
  rule_auto rule_cprop_235

/-- `cprop.isle:238`. -/
theorem ok_rule_cprop_238 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_238 := by
  rule_auto rule_cprop_238

/-- `cprop.isle:241`. -/
theorem ok_rule_cprop_241 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_241 := by
  rule_auto rule_cprop_241

/-- `cprop.isle:247`. -/
theorem ok_rule_cprop_247 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_247 := by
  rule_auto rule_cprop_247

/-- `cprop.isle:249`. -/
theorem ok_rule_cprop_249 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_249 := by
  rule_auto rule_cprop_249

/-- `cprop.isle:252`. -/
theorem ok_rule_cprop_252 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_252 := by
  rule_auto rule_cprop_252

/-- `cprop.isle:254`. -/
theorem ok_rule_cprop_254 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_254 := by
  rule_auto rule_cprop_254

/-- `cprop.isle:257`. -/
theorem ok_rule_cprop_257 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_257 := by
  rule_auto rule_cprop_257

/-- `cprop.isle:259`. -/
theorem ok_rule_cprop_259 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_259 := by
  rule_auto rule_cprop_259

/-- `cprop.isle:333`. -/
theorem ok_rule_cprop_333 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_333 := by
  rule_auto rule_cprop_333

/-- `cprop.isle:337`. -/
theorem ok_rule_cprop_337 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_337 := by
  rule_auto rule_cprop_337

/-- `cprop.isle:341`. -/
theorem ok_rule_cprop_341 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_341 := by
  rule_auto rule_cprop_341

/-- `cprop.isle:345`. -/
theorem ok_rule_cprop_345 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_345 := by
  rule_auto rule_cprop_345

/-- `cprop.isle:349`. -/
theorem ok_rule_cprop_349 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_349 := by
  rule_auto rule_cprop_349

/-- `cprop.isle:521`. -/
theorem ok_rule_cprop_521 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_521 := by
  rule_auto rule_cprop_521

end Opt.Proof
