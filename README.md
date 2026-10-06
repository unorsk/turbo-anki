# turbo-anki

Spaced repetition in the terminal, written in Lean 4. It has two kinds of deck:

| Kind | How you study | Rating |
|---|---|---|
| **Flashcards** | See the front, reveal the back | You rate 1–4 (Again / Hard / Good / Easy) |
| **Dictionary** | See the translation, type the word, three passes (melk's drill) | Computed from what you typed |

Scheduling is FSRS-5, ported line by line from melk (`melk2/server/src/fsrs.ts`), so
migrated cards carry on exactly where they were.

Dependencies: [hyper-vision](https://github.com/unorsk/hyper-vision) (the Turbo
Vision–style interface), [leanline](https://github.com/unorsk/leanline) (line editing
for the terminal drill) and [leansqlite](https://github.com/leanprover/leansqlite)
(storage). Nothing else.

## Running

```sh
lake build                          # also checks every proof
.lake/build/bin/turbo-anki          # the full-screen interface
lake test                           # unit tests, UI scenarios, migration test
```

Data lives in `~/.local/share/turbo-anki/turbo-anki.db` (or `$XDG_DATA_HOME/...`, or
`$TURBO_ANKI_DB`, or `--db <path>`).

### The full-screen interface

The **Decks** window lists every deck with its due, new and total counts.

| Key | |
|---|---|
| `Enter` / `S` | Study the selected deck: due cards, or new ones if nothing is due |
| `R` / `L` | Review due cards / learn new ones |
| `C` | Browse and edit the deck's cards |
| `N`, `M`, `D` | New deck, rename, delete (asks first) |
| `I` | Import a `front##back` (or tab-separated) word file |
| `F2` | Back to the deck overview · `F6` next window · `F10` menu · `Alt-X` exit |

**Studying flashcards.** `Space`/`Enter` shows the answer; `1`–`4` rate it. Each button
shows when the card would come back. A card still in its learning steps (due again within
minutes) is shown again later in the session; a card that graduates leaves it.

**Drilling a dictionary.** Type the word for the translation shown and press `Enter`. The
session's cards (twelve, as in melk) are shuffled and asked three times over. Only the
first answer to a card counts as its review: exact → Good, a typo → Hard, wrong → Again.
A typo is an accent slip (`far` for `får`), or one edit on words up to four letters and
two on longer ones, with a swap of two letters counting as one edit. Case, punctuation and
spacing are ignored. A correct answer is not commented on: the next question just
appears. A typo shows the right spelling under the next question. A wrong answer shows
the word in red until you press `Enter`, and sends the card to the back of the queue, so
every word ends up typed correctly three times.

**Editing.** In a card browser, `Alt-F` searches (front and back), `Enter` on a card
edits it, `A` adds cards (the dialog stays open for the next one), `D` deletes, and `R`
resets a card to new. Editing a card keeps its schedule and history.

### The command line

```
turbo-anki decks                              decks with counts
turbo-anki drill <deck> [--new] [--limit N]   melk's terminal drill (leanline)
turbo-anki create-deck <name> [--dictionary]
turbo-anki import <deck> <file>               front##back lines; idempotent
turbo-anki migrate-melk <dump>                import melk's data (below)
turbo-anki import-anki [<collection>]         Anki's cards as new flashcards
```

`import-anki` reads a copy of an Anki collection (default: profile “User 1”) and adds
each deck's cards, as new cards without their Anki history, to a flashcard deck of the
same name (`Parent::Child` for nested decks). Fields are converted from HTML to text.
Cloze notes and cards of note types with more than two cards are listed and skipped.

## Migrating from melk

```sh
cd ../melk2/server
npx wrangler login                                  # once, if the token expired
npx wrangler d1 export melk --remote --output melk.sql
cd -
.lake/build/bin/turbo-anki migrate-melk ../melk2/server/melk.sql
```

Every deck becomes a dictionary deck. Every card keeps its full FSRS state (due date to
the millisecond, stability, difficulty, reps, lapses), and its review log comes along.
Afterwards the command prints melk's due/new/total counts next to turbo-anki's, deck by
deck. Running it again changes nothing (decks are matched by name, cards by front).

## What is proved

`lake build` checks these theorems:

- **Edit distance** (`Proofs/Distance`, `Core/Distance`): the O(n·m) dynamic programme
  equals the recursive specification (and replaces it in compiled code via `@[csimp]`).
  The distance is zero exactly on equal texts, is symmetric, lies between the difference
  in length and the longer length.
- **Grading** (`Proofs/Grade`): correct ⇔ the normalized answer is non-empty and equal to
  the expected one; typing the answer is correct; an empty answer is wrong; a typo is
  within two edits (one on short words) or an accent slip; typing can never earn Easy.
- **Scheduling** (`Proofs/Fsrs`): a review always schedules the card strictly in the
  future; a card is in the review phase exactly when it is scheduled whole days
  (1 to 36 502) ahead, otherwise within minutes; Again never schedules days ahead, Easy
  always does; from review Hard < Good < Easy; every review counts one rep; only
  forgetting a review card counts a lapse.
- **Sessions** (`Proofs/Session`): shuffling is a permutation. A drill keeps the
  invariant "correct answers + remaining appearances = 3 per card", so a finished
  drill has had every card typed correctly exactly three times. Each card gets exactly
  one rating, from its first answer, and it never changes, and at the end every card has
  one. A flashcard leaves the session exactly when it graduates.
- **Storage** (`Proofs/Store`): what the store writes for a card it reads back
  unchanged, so a card's schedule never drifts through the database.
- **hyper-vision's list box**: after any key or mouse event its focus is on an item and
  visible.

The floating-point memory model (stability, difficulty) cannot be proved in Lean, so it
is tested against golden vectors generated by melk's own scheduler
(`scripts/fsrs_golden.ts`). Grading is tested against melk's own test cases.

## Layout

```
TurboAnki/Core/     time, FSRS, text normalization, edit distance, grading, sessions, model
TurboAnki/Proofs/   the theorems above
TurboAnki/Store     SQLite schema and queries (leansqlite)
TurboAnki/Ui/       the hyper-vision interface: pure window builders + command handler
TurboAnki/Cli       subcommands and the leanline drill
TurboAnki/Migrate   melk import
TurboAnkiTests/     compile-time unit tests, headless UI scenarios, migration test
scripts/            Unicode table generator, FSRS golden-vector generator (dev only)
```
