import FV.Opt.Basic
import FV.Isle.Opt.Simplify

/-!
# The rewrite-rule interface

A rule set is Cranelift's `simplify` multi-constructor seen from the driver
(`FV/Opt/Simplify.lean`): given the value `v` of a freshly inserted pure node, return the
values equivalent to `v` that the rules produce. The graph is abstract (`σ`):

* `enodes st x`: the pure nodes defining `x` (`inst_data_value`; empty for block parameters
  and skeleton results). Operands are value ids.
* `typeOf st x`: the type of `x` (`value_type`; `i8` for `icmp`).
* `make st n`: `make_inst` — insert the pure node `n` (the driver hash-conses it and
  recursively simplifies it) and return its value.

Result: candidates `(value, subsume)` in rule order, the names of the rules that produced them,
and the new graph state. `.error` only for interpreter failures (an unmodelled extern, fuel).

Implementations: the exported Cranelift rules (`Isle.Opt.simplify`, `docs/contracts/isle.md`)
and `Opt.HandRules.simplify` (a small hand-written stand-in).

**Proof obligation of a rule set** (`docs/contracts/midend.md`): every candidate `w` of `v`
evaluates, in every register file where the nodes reachable from `v` evaluate, to the same
value as `v` (and has the same type), and every node passed to `make` has operands among
the values reachable from `v` (or made earlier), so it can be placed where `v` is defined.
-/

namespace Opt

open Clif

abbrev SimplifyFn := {σ : Type} → (σ → ValueId → List Inst) → (σ → ValueId → Option Ty) →
  (σ → Inst → ValueId × σ) → σ → ValueId → Except String (List (ValueId × Bool) × List String × σ)

/-- Cranelift's `simplify_skeleton`: simplifications of a side-effecting instruction or a
terminator (`Isle.Opt.SkelInst`), e.g. `udiv x, 8 ⇒ ushr x, 3` (`removeWithVal`),
`brif 1, b1, b2 ⇒ jump b1` (`replace`), `brif c, trap_block, b ⇒ trapnz c; jump b`
(`replaceWithTwo`). The extra callback is `just_trap_block`: the trap code of a block whose
body is pure and whose terminator is `trap`.

**Proof obligation:** each simplification is equivalent to the original instruction (same
results, same trap behaviour, same successor with the same arguments) in every state where
the nodes reachable from its operands evaluate. -/
abbrev SkeletonFn := {σ : Type} → (σ → ValueId → List Inst) → (σ → ValueId → Option Ty) →
  (σ → Inst → ValueId × σ) → (σ → BlockId → Option TrapCode) → σ → Isle.Opt.SkelInst →
  Except String (List Isle.Opt.SkelSimp × List String × σ)

/-- The available rule sets (`Opt.RuleSetId.fn` in `FV/Opt/Optimize.lean`). -/
inductive RuleSetId where
  /-- Cranelift 0.136.1's `simplify` rules, exported (`Isle.Opt.program`) and run by the ISLE
  multi-term interpreter (`Isle.Opt.simplify`, `docs/contracts/isle.md`). -/
  | cranelift
  /-- `Opt.HandRules.simplify`. -/
  | hand
  deriving DecidableEq, Repr, Inhabited

def RuleSetId.name : RuleSetId → String
  | .cranelift => "cranelift"
  | .hand => "hand"

def RuleSetId.all : List RuleSetId := [.cranelift, .hand]

/-- Ids (`Isle.Rule.id`) of the exported `simplify` rules whose correctness is proven
(`Opt.Proof.simplifyRulesCorrect_proven`, `FV/Opt/Proof/RuleAll.lean`): the rules proven in
`FV/Opt/Proof/RuleArith.lean`, `RuleCprop.lean` and `RuleBitops1.lean`..`RuleBitops7.lean`. -/
def provenSimplifyRules : List Nat :=
  [65, 66, 67, 68, 69, 70, 71, 72, 78, 111, 113, 114, 115, 116, 117, 126, 127, 128, 129, 130, 131,
   132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 152, 153, 154, 155, 157,
   159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177,
   178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 203, 222, 223, 224, 225, 226, 227, 228,
   229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247,
   248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266,
   267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
   286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304,
   305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 334, 354,
   355, 356, 357, 358, 359, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 375, 376, 377, 378,
   393, 394, 395, 396, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412,
   413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
   432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450,
   451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469,
   470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488,
   489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507,
   508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526,
   527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545,
   546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564,
   565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583,
   584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602,
   603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621,
   622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640,
   641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659,
   660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678,
   679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697,
   698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716,
   717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735,
   736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754,
   755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773,
   774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792,
   793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811,
   812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 828, 829, 830, 831, 837, 838, 839,
   840, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862,
   863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 895, 896, 897, 898,
   899, 945]

/-- Which exported rules may contribute candidates (`Isle.Opt.simplify`'s allow-list); the other
rules still run, their candidates are dropped. -/
inductive RuleAllow where
  /-- Every rule (default; not yet proven). -/
  | all
  /-- Only `provenSimplifyRules` (no skeleton rule is proven yet, so none contributes). -/
  | proven
  /-- An explicit list of rule ids. -/
  | ids (l : List Nat)
  deriving DecidableEq, Repr, Inhabited

def RuleAllow.pred : RuleAllow → Nat → Bool
  | .all => fun _ => true
  | .proven => fun r => provenSimplifyRules.contains r
  | .ids l => fun r => l.contains r

end Opt
