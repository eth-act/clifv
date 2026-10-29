module

@[expose] public section

/-!
# The module-system header of generated Lean files

The Lean generators (`FVTest/Backend/*Gen*.lean`, `FVTest/Backend/Proof/Probe/GenData.lean`,
`FVTest/Opt/Proof/GenData.lean`) write their files' text with plain `import` lines;
`Gen.moduleHeader` turns that text into the form `scripts/module-port.py` gives every checked-in
module: `module`, `public import` for each import, `@[expose] public section` after the imports.
-/

namespace Gen

/-- `module` before the leading `import` lines, `public` on each, then `@[expose] public section`
(blank lines after the imports dropped), as `scripts/module-port.py` ports a file whose imports
come first. Text without leading imports is returned unchanged. -/
def moduleHeader (s : String) : String :=
  let ls := s.splitOn "\n"
  let imps := ls.takeWhile (·.startsWith "import ")
  if imps.isEmpty then s else
  let rest := (ls.drop imps.length).dropWhile (·.all Char.isWhitespace)
  "\n".intercalate (["module", ""] ++ imps.map ("public " ++ ·) ++
    ["", "@[expose] public section", ""] ++ rest)

end Gen
