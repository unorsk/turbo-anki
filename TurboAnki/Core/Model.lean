import TurboAnki.Core.Fsrs

/-!
# Decks and cards

The domain types shared by the store and the user interfaces.
-/

namespace TurboAnki

structure DeckId where
  val : Int64
deriving DecidableEq, Hashable, Repr, Inhabited

structure CardId where
  val : Int64
deriving DecidableEq, Hashable, Repr, Inhabited

/-- The two kinds of deck, which differ in how they are studied. -/
inductive DeckKind where
  /-- Front and back; the answer is revealed and rated by hand (Anki-style). -/
  | flashcards
  /-- Words and translations; the word is typed and graded automatically, in a drill of
  three passes (melk-style). -/
  | dictionary
deriving DecidableEq, Repr, Inhabited

namespace DeckKind

/-- How the store spells the kind. -/
def code : DeckKind → String
  | flashcards => "flashcards"
  | dictionary => "dictionary"

def ofCode? : String → Option DeckKind
  | "flashcards" => some flashcards
  | "dictionary" => some dictionary
  | _ => none

theorem ofCode?_code (k : DeckKind) : ofCode? k.code = some k := by
  cases k <;> rfl

def label : DeckKind → String
  | flashcards => "Flashcards"
  | dictionary => "Dictionary"

end DeckKind

structure Deck where
  id : DeckId
  name : String
  kind : DeckKind
  tag : String := ""
deriving Repr, Inhabited

/-- Card counts of a deck at some instant. -/
structure DeckStats where
  total : Nat
  due : Nat
  new : Nat
deriving Repr, Inhabited, DecidableEq

structure Card where
  id : CardId
  deckId : DeckId
  front : String
  back : String
  sched : Sched
deriving Repr, Inhabited

/-- What a session studies. -/
inductive Mode where
  /-- Cards whose review is due. -/
  | review
  /-- Cards never studied. -/
  | learn
deriving DecidableEq, Repr, Inhabited

/-- How many cards a session takes: melk's twelve words for a drill, and enough
flashcards for a sitting. -/
def sessionLimit : DeckKind → Mode → Nat
  | .dictionary, _ => 12
  | .flashcards, .review => 100
  | .flashcards, .learn => 20

/-- A front/back pair to import, as in melk's `front##back` word files. -/
structure Pair where
  front : String
  back : String
deriving Repr, Inhabited, DecidableEq

/-- Parses one line of a word file: `front##back`, or `front<TAB>back`. Blank lines and
lines without exactly one separator are not pairs. -/
def Pair.parse? (line : String) : Option Pair :=
  let line := line.trimAscii.toString
  if line.isEmpty then none else
  let split (sep : String) : Option Pair :=
    match line.splitOn sep with
    | [f, b] =>
      let f := f.trimAscii.toString
      let b := b.trimAscii.toString
      if f.isEmpty || b.isEmpty then none else some { front := f, back := b }
    | _ => none
  split "##" <|> split "\t"

end TurboAnki
