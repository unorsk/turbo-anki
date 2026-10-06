import TurboAnkiTests

/-!
The test driver (`lake test`). Building it checks the compile-time unit tests; running
it plays the UI scenarios and the melk migration against scratch databases.
Pass `-v` to see the screens the UI test goes through.
-/

def main (args : List String) : IO UInt32 := do
  let dir ← IO.FS.createTempDir
  try
    TurboAnkiTests.Ui.run (args.contains "-v") (dir / "ui.db")
    TurboAnkiTests.Migrate.run dir
    return 0
  catch e =>
    IO.eprintln e
    return 1
  finally
    IO.FS.removeDirAll dir
