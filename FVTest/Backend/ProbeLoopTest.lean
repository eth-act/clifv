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

## The same frame compiled both ways (#1013)

Cranelift probes only with `enable_probestack` (`StackProbe.off` without it). The words are
stock Cranelift's (wasmtime v49.0.1, the artifacts of the stock comparison, run 43441554902):

* a 100016-byte frame without probes: `isa/aarch64/stack.clif` `%stack_addr_big`
  (`enable_probestack=false`), `stp; mov x29, sp; mov w16, #0x86b0; movk w16, #1, lsl #16;
  sub sp, sp, x16`; with probes the loop comes before the `sp` adjustment;
* a 100000-byte frame with probes: `isa/aarch64/inline-probestack.clif` `%large`
  (`enable_probestack=true`, inline, 4 KiB guard);
* a 12288-byte frame with probes: the same file's `%unrolled` (three unrolled probes); without,
  the frame setup and `sub sp, sp, #3, lsl #12`.
-/

namespace Backend.ProbeLoopTest

open Backend

/-- No labels; the instruction at offset 0. -/
def env0 : Env := ⟨0, fun _ => none⟩

/-- The machine words of a line list (instruction lines only). -/
def wordsOf (ls : List Line) : List (Option (BitVec 32)) :=
  ls.filterMap fun | .ins i _ => some (i.encode env0).toOption | _ => none

#guard wordsOf (prologueLines [.x 19] 16400 .caller) = ([0xa9bf7bfd, 0x910003fd, 0xd2800010, 0xd2880411,
  0xd1400610, 0xb8306bff, 0xab11021f, 0x54ffffac, 0xf81f0ff3, 0xd14013ff] : List (BitVec 32)).map some

#guard wordsOf (prologueLines [.x 19, .x 20, .x 21] 24624 .caller) = ([0xa9bf7bfd, 0x910003fd, 0xd2800010,
  0xd28c0811, 0xd1400610, 0xb8306bff, 0xab11021f, 0x54ffffac, 0xf81f0ff5, 0xa9bf53f3, 0xd28c0210,
  0xcb3063ff] : List (BitVec 32)).map some

-- the loop form starts at 16 KiB of probed stack (four probes); below, the unrolled form
#guard probeCount 16384 = 4 && probeCount 16383 = 3 && probeCount 16416 = 5

-- #1013: one frame, both settings
#guard wordsOf (prologueLines [] 100016 .off) = ([0xa9bf7bfd, 0x910003fd, 0x5290d610, 0x72a00030,
  0xcb3063ff] : List (BitVec 32)).map some

#guard wordsOf (prologueLines [] 100016 .leaf) = ([0xa9bf7bfd, 0x910003fd, 0xd2800010, 0x5290d611,
  0x72a00031, 0xd1400610, 0xb8306bff, 0xab11021f, 0x54ffffac, 0x5290d610, 0x72a00030,
  0xcb3063ff] : List (BitVec 32)).map some

#guard wordsOf (prologueLines [] 100000 .leaf) = ([0xa9bf7bfd, 0x910003fd, 0xd2800010, 0x5290d411,
  0x72a00031, 0xd1400610, 0xb8306bff, 0xab11021f, 0x54ffffac, 0x5290d410, 0x72a00030,
  0xcb3063ff] : List (BitVec 32)).map some

#guard wordsOf (prologueLines [] 12288 .leaf) = ([0xa9bf7bfd, 0x910003fd, 0xd14007ff, 0xb80003ff,
  0xd14007ff, 0xb80003ff, 0xd14007ff, 0xb80003ff, 0x91400fff, 0xd1400fff] : List (BitVec 32)).map some

#guard wordsOf (prologueLines [] 12288 .off) = ([0xa9bf7bfd, 0x910003fd, 0xd1400fff] : List (BitVec 32)).map some

-- without probes nothing is probed, whatever the frame; with them a caller's probed stack
-- counts its callees' 16-byte setup area
#guard probeTotal 100016 .off = 0 && probeCount (probeTotal 100016 .off) = 0 &&
  probeCount (probeTotal 4080 .leaf) = 0 && probeCount (probeTotal 4080 .caller) = 1

end Backend.ProbeLoopTest
