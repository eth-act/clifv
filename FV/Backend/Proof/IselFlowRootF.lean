import FV.Backend.Proof.IselFlowTabF

/-!
# The root rules of `lower` against the flow table

The rules of `lower` (`data_program.r686`, in chunks to bound the kernel's memory) other than `nop`'s (587) check with the root instruction (`⟨1, true⟩`) and return a value of flow level
at most `1`.
-/

namespace Backend.Proof.Flow

open Isle Isle.Aarch64 Backend.Proof

/-- Rules 0… of `lower`. -/
def flowRules0 : List Rule :=
  [rule_lower_419, rule_lower_402, rule_lower_1444, rule_lower_1481, rule_lower_116, rule_lower_125,
   rule_lower_1442, rule_lower_1479, rule_lower_2779, rule_lower_120, rule_lower_128, rule_lower_165,
   rule_lower_1439, rule_lower_1476, rule_lower_2784, rule_lower_93, rule_lower_167, rule_lower_1437,
   rule_lower_1474, rule_lower_1501, rule_lower_1507, rule_lower_2789, rule_lower_3091, rule_lower_3155,
   rule_lower_90]

/-- Rules 25… of `lower`. -/
def flowRules1 : List Rule :=
  [rule_lower_169, rule_lower_1435, rule_lower_1472, rule_lower_1540, rule_lower_2152, rule_lower_2793,
   rule_lower_3097, rule_lower_3161, rule_lower_102, rule_lower_171, rule_lower_1408, rule_lower_1434,
   rule_lower_1471, rule_lower_1539, rule_lower_2158, rule_lower_2185, rule_lower_2798, rule_lower_2828,
   rule_lower_3008, rule_lower_3101, rule_lower_3165, rule_lower_98, rule_lower_190, rule_lower_437,
   rule_lower_609]

/-- Rules 50… of `lower`. -/
def flowRules2 : List Rule :=
  [rule_lower_810, rule_lower_861, rule_lower_1163, rule_lower_1222, rule_lower_1224, rule_lower_1226,
   rule_lower_1228, rule_lower_1406, rule_lower_1431, rule_lower_1468, rule_lower_1536, rule_lower_2120,
   rule_lower_2164, rule_lower_2191, rule_lower_2386, rule_lower_2404, rule_lower_2419, rule_lower_2435,
   rule_lower_2815, rule_lower_3018, rule_lower_3036, rule_lower_3056, rule_lower_3076, rule_lower_3126,
   rule_lower_3140]

/-- Rules 75… of `lower`. -/
def flowRules3 : List Rule :=
  [rule_lower_3190, rule_lower_3204, rule_lower_111, rule_lower_203, rule_lower_205, rule_lower_207,
   rule_lower_209, rule_lower_211, rule_lower_213, rule_lower_215, rule_lower_217, rule_lower_222,
   rule_lower_224, rule_lower_226, rule_lower_228, rule_lower_230, rule_lower_232, rule_lower_240,
   rule_lower_242, rule_lower_244, rule_lower_246, rule_lower_248, rule_lower_250, rule_lower_260,
   rule_lower_262]

/-- Rules 100… of `lower`. -/
def flowRules4 : List Rule :=
  [rule_lower_264, rule_lower_266, rule_lower_268, rule_lower_270, rule_lower_294, rule_lower_300,
   rule_lower_440, rule_lower_608, rule_lower_693, rule_lower_699, rule_lower_707, rule_lower_713,
   rule_lower_730, rule_lower_733, rule_lower_750, rule_lower_753, rule_lower_767, rule_lower_773,
   rule_lower_787, rule_lower_793, rule_lower_816, rule_lower_857, rule_lower_1056, rule_lower_1068,
   rule_lower_1116]

/-- Rules 125… of `lower`. -/
def flowRules5 : List Rule :=
  [rule_lower_1167, rule_lower_1236, rule_lower_1242, rule_lower_1248, rule_lower_1254, rule_lower_1266,
   rule_lower_1272, rule_lower_1281, rule_lower_1283, rule_lower_1401, rule_lower_1429, rule_lower_1466,
   rule_lower_1534, rule_lower_1704, rule_lower_1707, rule_lower_1803, rule_lower_1808, rule_lower_2138,
   rule_lower_2170, rule_lower_2197, rule_lower_2288, rule_lower_2328, rule_lower_2331, rule_lower_2334,
   rule_lower_2337]

/-- Rules 150… of `lower`. -/
def flowRules6 : List Rule :=
  [rule_lower_2340, rule_lower_2343, rule_lower_2346, rule_lower_2349, rule_lower_2352, rule_lower_2381,
   rule_lower_2400, rule_lower_2415, rule_lower_2431, rule_lower_2451, rule_lower_2466, rule_lower_2508,
   rule_lower_2580, rule_lower_2803, rule_lower_2822, rule_lower_2837, rule_lower_3014, rule_lower_3031,
   rule_lower_3051, rule_lower_3071, rule_lower_3110, rule_lower_3174, rule_lower_53, rule_lower_58,
   rule_lower_63]

/-- Rules 175… of `lower`. -/
def flowRules7 : List Rule :=
  [rule_lower_68, rule_lower_73, rule_lower_78, rule_lower_108, rule_lower_132, rule_lower_273,
   rule_lower_279, rule_lower_284, rule_lower_308, rule_lower_313, rule_lower_316, rule_lower_336,
   rule_lower_342, rule_lower_368, rule_lower_375, rule_lower_379, rule_lower_383, rule_lower_387,
   rule_lower_450, rule_lower_463, rule_lower_477, rule_lower_485, rule_lower_493, rule_lower_501,
   rule_lower_509]

/-- Rules 200… of `lower`. -/
def flowRules8 : List Rule :=
  [rule_lower_517, rule_lower_525, rule_lower_533, rule_lower_541, rule_lower_549, rule_lower_554,
   rule_lower_559, rule_lower_567, rule_lower_570, rule_lower_578, rule_lower_581, rule_lower_589,
   rule_lower_592, rule_lower_600, rule_lower_603, rule_lower_685, rule_lower_690, rule_lower_696,
   rule_lower_704, rule_lower_710, rule_lower_724, rule_lower_727, rule_lower_744, rule_lower_747,
   rule_lower_764]

/-- Rules 225… of `lower`. -/
def flowRules9 : List Rule :=
  [rule_lower_770, rule_lower_784, rule_lower_790, rule_lower_805, rule_lower_836, rule_lower_841,
   rule_lower_846, rule_lower_851, rule_lower_865, rule_lower_906, rule_lower_914, rule_lower_995,
   rule_lower_1000, rule_lower_1005, rule_lower_1010, rule_lower_1015, rule_lower_1020, rule_lower_1025,
   rule_lower_1030, rule_lower_1035, rule_lower_1040, rule_lower_1045, rule_lower_1050, rule_lower_1059,
   rule_lower_1071]

/-- Rules 250… of `lower`. -/
def flowRules10 : List Rule :=
  [rule_lower_1119, rule_lower_1145, rule_lower_1190, rule_lower_1204, rule_lower_1233, rule_lower_1239,
   rule_lower_1245, rule_lower_1251, rule_lower_1294, rule_lower_1300, rule_lower_1339, rule_lower_1359,
   rule_lower_1391, rule_lower_1424, rule_lower_1461, rule_lower_1528, rule_lower_1549, rule_lower_1553,
   rule_lower_1642, rule_lower_1646, rule_lower_1699, rule_lower_1720, rule_lower_1791, rule_lower_1797,
   rule_lower_1827]

/-- Rules 275… of `lower`. -/
def flowRules11 : List Rule :=
  [rule_lower_1857, rule_lower_1862, rule_lower_1916, rule_lower_1931, rule_lower_1937, rule_lower_1940,
   rule_lower_1951, rule_lower_1955, rule_lower_1958, rule_lower_1982, rule_lower_1986, rule_lower_1989,
   rule_lower_2000, rule_lower_2004, rule_lower_2016, rule_lower_2035, rule_lower_2038, rule_lower_2041,
   rule_lower_2044, rule_lower_2052, rule_lower_2074, rule_lower_2080, rule_lower_2086, rule_lower_2092,
   rule_lower_2099]

/-- Rules 300… of `lower`. -/
def flowRules12 : List Rule :=
  [rule_lower_2108, rule_lower_2113, rule_lower_2146, rule_lower_2176, rule_lower_2203, rule_lower_2237,
   rule_lower_2242, rule_lower_2262, rule_lower_2267, rule_lower_2280, rule_lower_2285, rule_lower_2301,
   rule_lower_2304, rule_lower_2307, rule_lower_2310, rule_lower_2316, rule_lower_2321, rule_lower_2357,
   rule_lower_2359, rule_lower_2361, rule_lower_2363, rule_lower_2365, rule_lower_2367, rule_lower_2369,
   rule_lower_2371]

/-- Rules 325… of `lower`. -/
def flowRules13 : List Rule :=
  [rule_lower_2373, rule_lower_2375, rule_lower_2377, rule_lower_2390, rule_lower_2395, rule_lower_2408,
   rule_lower_2423, rule_lower_2439, rule_lower_2446, rule_lower_2454, rule_lower_2461, rule_lower_2469,
   rule_lower_2476, rule_lower_2481, rule_lower_2486, rule_lower_2491, rule_lower_2496, rule_lower_2499,
   rule_lower_2502, rule_lower_2518, rule_lower_2529, rule_lower_2574, rule_lower_2587, rule_lower_2595,
   rule_lower_2604]

/-- Rules 350… of `lower`. -/
def flowRules14 : List Rule :=
  [rule_lower_2607, rule_lower_2610, rule_lower_2613, rule_lower_2619, rule_lower_2647, rule_lower_2650,
   rule_lower_2653, rule_lower_2656, rule_lower_2659, rule_lower_2662, rule_lower_2666, rule_lower_2672,
   rule_lower_2678, rule_lower_2684, rule_lower_2690, rule_lower_2696, rule_lower_2705, rule_lower_2709,
   rule_lower_2713, rule_lower_2717, rule_lower_2722, rule_lower_2726, rule_lower_2730, rule_lower_2735,
   rule_lower_2770]

/-- Rules 375… of `lower`. -/
def flowRules15 : List Rule :=
  [rule_lower_2773, rule_lower_2809, rule_lower_2818, rule_lower_2842, rule_lower_2849, rule_lower_2863,
   rule_lower_2887, rule_lower_2900, rule_lower_2913, rule_lower_2927, rule_lower_3022, rule_lower_3042,
   rule_lower_3062, rule_lower_3082, rule_lower_3217, rule_lower_3220, rule_lower_3225, rule_lower_3286,
   rule_lower_3292, rule_lower_dynamic_neon_81, rule_lower_dynamic_neon_87, rule_lower_86, rule_lower_319, rule_lower_359,
   rule_lower_390]

/-- Rules 400… of `lower`. -/
def flowRules16 : List Rule :=
  [rule_lower_434, rule_lower_472, rule_lower_482, rule_lower_490, rule_lower_498, rule_lower_506,
   rule_lower_514, rule_lower_522, rule_lower_530, rule_lower_538, rule_lower_546, rule_lower_564,
   rule_lower_575, rule_lower_586, rule_lower_597, rule_lower_718, rule_lower_721, rule_lower_738,
   rule_lower_741, rule_lower_758, rule_lower_761, rule_lower_778, rule_lower_781, rule_lower_831,
   rule_lower_876]

/-- Rules 425… of `lower`. -/
def flowRules17 : List Rule :=
  [rule_lower_956, rule_lower_1153, rule_lower_1197, rule_lower_1211, rule_lower_1289, rule_lower_1349,
   rule_lower_1387, rule_lower_1421, rule_lower_1458, rule_lower_1525, rule_lower_1545, rule_lower_1638,
   rule_lower_1736, rule_lower_1778, rule_lower_1844, rule_lower_1848, rule_lower_1946, rule_lower_1961,
   rule_lower_1995, rule_lower_2030, rule_lower_2179, rule_lower_2209, rule_lower_2294, rule_lower_2622,
   rule_lower_2742]

/-- Rules 450… of `lower`. -/
def flowRules18 : List Rule :=
  [rule_lower_dynamic_neon_43, rule_lower_dynamic_neon_57, rule_lower_dynamic_neon_71, rule_lower_dynamic_neon_92, rule_lower_dynamic_neon_97, rule_lower_137,
   rule_lower_322, rule_lower_826, rule_lower_924, rule_lower_1261, rule_lower_1329, rule_lower_1385,
   rule_lower_1419, rule_lower_1456, rule_lower_1523, rule_lower_1588, rule_lower_1661, rule_lower_1734,
   rule_lower_1772, rule_lower_1852, rule_lower_2215, rule_lower_2298, rule_lower_2625, rule_lower_2746,
   rule_lower_dynamic_neon_15]

/-- Rules 475… of `lower`. -/
def flowRules19 : List Rule :=
  [rule_lower_dynamic_neon_19, rule_lower_dynamic_neon_23, rule_lower_dynamic_neon_27, rule_lower_dynamic_neon_31, rule_lower_dynamic_neon_35, rule_lower_dynamic_neon_39,
   rule_lower_dynamic_neon_53, rule_lower_dynamic_neon_67, rule_lower_142, rule_lower_821, rule_lower_871, rule_lower_1320,
   rule_lower_1381, rule_lower_1452, rule_lower_1519, rule_lower_1583, rule_lower_1659, rule_lower_1729,
   rule_lower_1840, rule_lower_2628, rule_lower_2750, rule_lower_dynamic_neon_47, rule_lower_dynamic_neon_61, rule_lower_dynamic_neon_75,
   rule_lower_801]

/-- Rules 500… of `lower`. -/
def flowRules20 : List Rule :=
  [rule_lower_1315, rule_lower_1377, rule_lower_1415, rule_lower_1449, rule_lower_1516, rule_lower_1654,
   rule_lower_1695, rule_lower_2633, rule_lower_2754, rule_lower_dynamic_neon_3, rule_lower_dynamic_neon_11, rule_lower_1412,
   rule_lower_2638, rule_lower_2759, rule_lower_dynamic_neon_7, rule_lower_2643, rule_lower_2763]

set_option maxRecDepth 100000 in
theorem flowRules_eq : program.rulesOf TId.lower = flowRules0 ++ flowRules1 ++ flowRules2 ++ flowRules3 ++ flowRules4 ++ flowRules5 ++ flowRules6 ++ flowRules7 ++ flowRules8 ++ flowRules9 ++ flowRules10 ++ flowRules11 ++ flowRules12 ++ flowRules13 ++ flowRules14 ++ flowRules15 ++ flowRules16 ++ flowRules17 ++ flowRules18 ++ flowRules19 ++ flowRules20 := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  rfl

/-- The check of one root rule of `lower`. -/
def flowRootOk (r : Rule) : Bool :=
  !closureRootIds.contains r.id || r.id == 587 ||
    aRule program flowTab false [⟨1, true⟩] ⟨1, false⟩ r

set_option maxRecDepth 100000 in
theorem flowRules0_ok : flowRules0.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules1_ok : flowRules1.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules2_ok : flowRules2.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules3_ok : flowRules3.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules4_ok : flowRules4.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules5_ok : flowRules5.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules6_ok : flowRules6.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules7_ok : flowRules7.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules8_ok : flowRules8.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules9_ok : flowRules9.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules10_ok : flowRules10.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules11_ok : flowRules11.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules12_ok : flowRules12.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules13_ok : flowRules13.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules14_ok : flowRules14.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules15_ok : flowRules15.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules16_ok : flowRules16.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules17_ok : flowRules17.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules18_ok : flowRules18.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules19_ok : flowRules19.all flowRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem flowRules20_ok : flowRules20.all flowRootOk = true := by
  decide +kernel

theorem flowRoot_ok : (program.rulesOf TId.lower).all flowRootOk = true := by
  rw [flowRules_eq]
  simp only [List.all_append, flowRules0_ok, flowRules1_ok, flowRules2_ok, flowRules3_ok, flowRules4_ok, flowRules5_ok, flowRules6_ok, flowRules7_ok, flowRules8_ok, flowRules9_ok, flowRules10_ok, flowRules11_ok, flowRules12_ok, flowRules13_ok, flowRules14_ok, flowRules15_ok, flowRules16_ok, flowRules17_ok, flowRules18_ok, flowRules19_ok, flowRules20_ok, Bool.and_self]

end Backend.Proof.Flow
