import Lean.Elab.ParseImportsFast
/-- Parse the packaged source headers with the same Lean parser used by Lake. -/
def main (args : List String) : IO Unit := do
  let some list := args.head? | throw (IO.userError "expected a UTF-8 list of source files")
  for line in (←IO.FS.readFile list).splitOn "\n" do
    let path := line.trimAscii.toString
    unless path.isEmpty do
      let h ← Lean.parseImports' (←IO.FS.readFile path) path
      let deps := h.imports.toList.map fun i => i.module.toString
      IO.println (Lean.toJson (path,deps)).compress

