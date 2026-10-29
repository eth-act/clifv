module

public import FV.Backend.Proof.RelocProvCheck

@[expose] public section

/-!
# The name-provenance summary table and its kernel check (#216)

The summary table of the name-provenance analysis (`RelocProvCheck`): per internal term reached
from the closure's root rules of `lower` and from `lower_branch`, the abstract inputs and output
(`NA` fields `⟨e, g, u, i, s⟩`). Computed by an untrusted fixpoint inference outside the
repository (strict mode) and kept as literal data; every rule of every table term is checked by
kernel decisions, in chunks of 12 terms to bound the kernel's memory.
-/

namespace Backend.Proof.RelocProv

open Isle Isle.Aarch64

/-- Chunk 0 of `provTab`. -/
def provTab0 : Tab :=
  [(172, [⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (242, [⟨true, true, false, false, true⟩], ⟨true, true, false, false, true⟩),
   (243, [⟨false, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (246, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (249, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (250, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (251, [⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (254, [⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (255, [⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (256, [⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (294, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (305, [⟨false, false, false, false, true⟩], ⟨false, false, false, true, true⟩)]

/-- Chunk 1 of `provTab`. -/
def provTab1 : Tab :=
  [(306, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (307, [⟨false, false, false, false, true⟩], ⟨false, false, false, true, true⟩),
   (310, [⟨false, false, false, false, true⟩], ⟨false, false, false, true, true⟩),
   (344, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (358, [⟨false, true, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (359, [⟨false, true, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (360, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (361, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (362, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (363, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (370, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (371, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩)]

/-- Chunk 2 of `provTab`. -/
def provTab2 : Tab :=
  [(376, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (377, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (379, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (380, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (381, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (382, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (383, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (385, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (386, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (390, [⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (391, [⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (392, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩)]

/-- Chunk 3 of `provTab`. -/
def provTab3 : Tab :=
  [(393, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (395, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (406, [⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (407, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (409, [⟨false, true, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (410, [⟨false, false, false, true, true⟩], ⟨false, false, false, true, true⟩),
   (414, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (417, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (418, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (422, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (423, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (424, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩)]

/-- Chunk 4 of `provTab`. -/
def provTab4 : Tab :=
  [(425, [⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (426, [⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (428, [⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (430, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩, ⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (432, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (433, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (434, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (435, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (437, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (438, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (439, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (440, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩)]

/-- Chunk 5 of `provTab`. -/
def provTab5 : Tab :=
  [(443, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (444, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (451, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (452, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (466, [], ⟨false, false, false, true, true⟩),
   (469, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (473, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (487, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (488, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (489, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (490, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (491, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩)]

/-- Chunk 6 of `provTab`. -/
def provTab6 : Tab :=
  [(492, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (493, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (495, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (496, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (497, [⟨false, false, false, true, true⟩, ⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (498, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (501, [⟨false, false, false, true, true⟩, ⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (502, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (513, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (514, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (515, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (517, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩)]

/-- Chunk 7 of `provTab`. -/
def provTab7 : Tab :=
  [(518, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (520, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (521, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (522, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (524, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (528, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (529, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (530, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (531, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (532, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (533, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (534, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩)]

/-- Chunk 8 of `provTab`. -/
def provTab8 : Tab :=
  [(535, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (541, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (542, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (543, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (544, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (553, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩, ⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (555, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (556, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (557, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (558, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (559, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (560, [⟨false, false, false, false, true⟩], ⟨false, false, false, true, true⟩)]

/-- Chunk 9 of `provTab`. -/
def provTab9 : Tab :=
  [(561, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (562, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (564, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (565, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (566, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (570, [⟨true, true, false, false, true⟩, ⟨false, true, false, true, true⟩, ⟨true, true, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (571, [⟨true, true, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (572, [⟨true, true, false, false, true⟩, ⟨false, true, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (573, [⟨true, true, false, false, true⟩, ⟨false, true, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (574, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (575, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (576, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩)]

/-- Chunk 10 of `provTab`. -/
def provTab10 : Tab :=
  [(577, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (612, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (613, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (638, [⟨true, false, false, false, true⟩], ⟨true, false, false, false, true⟩),
   (639, [⟨true, false, false, false, true⟩], ⟨true, false, false, false, true⟩),
   (643, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (647, [⟨false, true, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (648, [⟨false, true, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (649, [⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (650, [⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (651, [⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (652, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩)]

/-- Chunk 11 of `provTab`. -/
def provTab11 : Tab :=
  [(653, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (654, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (655, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (656, [⟨false, false, false, false, true⟩], ⟨false, false, false, true, true⟩),
   (657, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, true, true⟩),
   (658, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (659, [⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (660, [⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (661, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (662, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (663, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (664, [⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩)]

/-- Chunk 12 of `provTab`. -/
def provTab12 : Tab :=
  [(665, [⟨false, true, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (666, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (667, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (668, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (669, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (670, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨true, true, false, false, true⟩),
   (698, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (699, [⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (700, [⟨false, false, false, false, true⟩, ⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (703, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (710, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (712, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩)]

/-- Chunk 13 of `provTab`. -/
def provTab13 : Tab :=
  [(715, [⟨false, true, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (722, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩)]

/-- Chunk 14 of `provTab`: the terms the S11e4 float data-movement roots reach (`output_value`,
`constant_f16/32/64`, `fpu_move_fp_imm`, `vec_dup_imm`, `fpu_load64`, the `aarch64_fpuload*`/
`aarch64_fpustore*` helpers), from the same fixpoint inference; S11e4 also widens
`mov_to_fpu`'s (409) first input to symbol names (`constant_f32`/`f64` pass it an `imm`). -/
def provTab14 : Tab :=
  [(173, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (586, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (587, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (537, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (546, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (538, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (547, [⟨false, true, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (375, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (411, [⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (585, [⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (681, [⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩)]

/-- Chunk 15 of `provTab`: the terms the S11f float arithmetic roots reach (`fpu_rr` 364,
`fpu_rrr` 368, `fpu_round` 408; operation and size enums, plain registers), checked like the
others. -/
def provTab15 : Tab :=
  [(364, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (368, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, true, true⟩], ⟨false, false, false, false, true⟩),
   (408, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩)]

/-- Chunk 16 of `provTab`: the terms the S11f-cvt conversion roots reach (`fpu_to_int_cvt_sat` 629, `signed_min`/`signed_max` 630/631, `fpu_to_int` 632, `int_to_fpu` 633). -/
def provTab16 : Tab :=
  [(629, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩, ⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (632, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (633, [⟨false, false, false, true, true⟩, ⟨false, false, false, false, true⟩], ⟨false, false, false, false, true⟩),
   (630, [⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩),
   (631, [⟨false, false, false, false, true⟩], ⟨false, true, false, false, true⟩)]

/-- The summary table. -/
def provTab : Tab := provTab0 ++ provTab1 ++ provTab2 ++ provTab3 ++ provTab4 ++ provTab5 ++ provTab6 ++ provTab7 ++ provTab8 ++ provTab9 ++ provTab10 ++ provTab11 ++ provTab12 ++ provTab13 ++ provTab14 ++ provTab15 ++ provTab16

set_option maxRecDepth 100000 in
theorem provTab0_ok :
    provTab0.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab1_ok :
    provTab1.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab2_ok :
    provTab2.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab3_ok :
    provTab3.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab4_ok :
    provTab4.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab5_ok :
    provTab5.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab6_ok :
    provTab6.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab7_ok :
    provTab7.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab8_ok :
    provTab8.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab9_ok :
    provTab9.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab10_ok :
    provTab10.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab11_ok :
    provTab11.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab12_ok :
    provTab12.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab13_ok :
    provTab13.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab14_ok :
    provTab14.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab15_ok :
    provTab15.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provTab16_ok :
    provTab16.all (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) =
      true := by
  decide +kernel

/-- Every rule of every term of `provTab` checks (strictly). -/
theorem provTab_ok : chkTab program provTab true = true := by
  unfold chkTab
  show (provTab0 ++ provTab1 ++ provTab2 ++ provTab3 ++ provTab4 ++ provTab5 ++ provTab6 ++ provTab7 ++ provTab8 ++ provTab9 ++ provTab10 ++ provTab11 ++ provTab12 ++ provTab13 ++ provTab14 ++ provTab15 ++ provTab16).all
    (fun e => (program.rulesOf e.1).all (aRule program provTab true e.2.1 e.2.2)) = true
  simp only [List.all_append, provTab0_ok, provTab1_ok, provTab2_ok, provTab3_ok, provTab4_ok, provTab5_ok, provTab6_ok, provTab7_ok, provTab8_ok, provTab9_ok, provTab10_ok, provTab11_ok, provTab12_ok, provTab13_ok, provTab14_ok, provTab15_ok, provTab16_ok, Bool.and_self]

end Backend.Proof.RelocProv
