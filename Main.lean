import TurboAnki

open TurboAnki

def main (argv : List String) : IO UInt32 := do
  let args := Cli.parseArgs ["db", "limit"] argv
  let opt (n : String) := (args.options.find? (·.1 == n)).map (·.2)
  try
    if args.flags.contains "help" || args.positional.head? == some "help" then
      IO.println Cli.usage
      return 0
    let path ← match opt "db" with
      | some p => pure (System.FilePath.mk p)
      | none => Store.defaultPath
    let store ← Store.openAt path
    match args.positional with
    | [] => Ui.App.run store
    | ["decks"] => Cli.listDecks store
    | ["drill", deck] =>
      let mode := if args.flags.contains "new" then Mode.learn else .review
      Cli.drill store deck mode ((opt "limit").bind String.toNat?)
    | ["create-deck", name] =>
      let kind := if args.flags.contains "dictionary" then DeckKind.dictionary else .flashcards
      match ← store.createDeck name kind (← Instant.now) with
      | .ok _ => IO.println s!"Created {kind.label.toLower} deck {name}."
      | .error e => throw <| IO.userError e.message
    | ["import", deck, file] => Cli.importFile store deck file
    | ["migrate-melk", dump] => Cli.migrateMelk store dump
    | ["import-anki"] => Cli.importAnki store none
    | ["import-anki", path] => Cli.importAnki store (some path)
    | _ =>
      IO.eprintln Cli.usage
      return 2
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1
