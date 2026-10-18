import FVTest.Link.LdArgs

/-! # `lake exe lean-ld ARGS…`: the Lean static linker (L2b stage 3, `Link.Ld.link`)

Takes the GNU ld arguments rustc gives `rust-lld -flavor gnu` for a static AArch64 musl
executable (docs/research/lean-linker.md §1, §6): objects, archives (rlibs, `-lc`, `-lunwind`
searched as `lib<name>.a` in every `-L` directory), `-o`, `-e`/`--entry`, `-u`/`--undefined`,
`--gc-sections`, `-Map`; options without effect on a static non-PIE link are accepted and
ignored (`--as-needed`, `-Bstatic`, `-Bdynamic`, `--eh-frame-hdr` (the header is always
written), `-z …`, `-static`, `-O1`, `--no-relax`, `-nostdlib`, …). `-pie`/`-shared` are errors
(`parseLdArgs`, `FVTest/Link/LdArgs.lean`).
-/

open Link.Ld

def main (args : List String) : IO UInt32 := do
  let c ← match ← parseLdArgs args with
    | .ok c => pure c
    | .error e => do IO.eprintln s!"lean-ld: {e}"; return 1
  match link c.opts c.ins with
  | .error e => IO.eprintln s!"lean-ld: {e}"; return 1
  | .ok r =>
    IO.FS.writeBinFile c.out r.img.write
    IO.setAccessRights c.out { user := { read := true, write := true, execution := true },
                               group := { read := true, execution := true },
                               other := { read := true, execution := true } }
    if let some m := c.mapPath then IO.FS.writeFile m r.map
    return 0
