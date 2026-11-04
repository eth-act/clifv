import FV.Backend.Asm
import FV.Backend.Encode

/-!
# The stack-probe loop's prologue against stock Cranelift (#581)

Two functions of `examples/deps` (crate `crypto_common`) whose probed stack is 16 KiB or more, so
that Cranelift emits the `StackProbeLoop` (`gen_probestack_loop`). The words are stock
Cranelift's (cg_clif's `cgclif.o` of the kept `cargo fv` temps, the first words of each
function); the `#guard`s check that `prologueLines` encodes to them:
`stp x29, x30, [sp, #-16]!; mov x29, sp; movz x16, #0; movz x17, #total;
sub x16, x16, #1, lsl #12; str wzr, [sp, x16]; cmn x16, x17; b.gt .-12`, then the pushes and the
`sp` adjustment.

* `_RNxC13crypto_common12H5Cvbuf0iCD1`: saves `x19`, frame 16400 bytes, calls (total 16416).
* `_RNxC13crypto_common12HaMs8ZRS9LA5`: saves `x19`–`x21`, frame 24624 bytes, calls (total
  24640); its `sp` adjustment 24592 is no `imm12`: `movz x16, #0x6010; sub sp, sp, x16`.
-/

namespace Backend.ProbeLoopTest

open Backend

/-- No labels; the instruction at offset 0. -/
def env0 : Env := ⟨0, fun _ => none⟩

/-- The machine words of a line list (instruction lines only). -/
def wordsOf (ls : List Line) : List (Option (BitVec 32)) :=
  ls.filterMap fun | .ins i _ => some (i.encode env0).toOption | _ => none

#guard wordsOf (prologueLines [.x 19] 16400 true) = ([0xa9bf7bfd, 0x910003fd, 0xd2800010, 0xd2880411,
  0xd1400610, 0xb8306bff, 0xab11021f, 0x54ffffac, 0xf81f0ff3, 0xd14013ff] : List (BitVec 32)).map some

#guard wordsOf (prologueLines [.x 19, .x 20, .x 21] 24624 true) = ([0xa9bf7bfd, 0x910003fd, 0xd2800010,
  0xd28c0811, 0xd1400610, 0xb8306bff, 0xab11021f, 0x54ffffac, 0xf81f0ff5, 0xa9bf53f3, 0xd28c0210,
  0xcb3063ff] : List (BitVec 32)).map some

-- the loop form starts at 16 KiB of probed stack (four probes); below, the unrolled form
#guard probeCount 16384 = 4 && probeCount 16383 = 3 && probeCount 16416 = 5

end Backend.ProbeLoopTest
