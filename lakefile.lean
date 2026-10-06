import Lake
open System Lake DSL

package «turbo-anki» where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
  testDriver := "tests"

require «hyper-vision» from git "https://github.com/unorsk/hyper-vision" @ "main"
require leanline from git "https://github.com/unorsk/leanline" @ "main"
require leansqlite from git "https://github.com/leanprover/leansqlite" @ "v4.34.0"

/-- The scheduler, the drills, the store and the user interfaces. Building it checks
every proof in `TurboAnki.Proofs`. -/
lean_lib TurboAnki

/-- Unit tests (checked at compile time) and the store's integration tests. -/
lean_lib TurboAnkiTests

/-- `lake test`: builds the unit tests, then runs the store tests against a scratch database. -/
lean_exe tests where
  root := `TurboAnkiTests.Main

@[default_target]
lean_exe «turbo-anki» where
  root := `Main
