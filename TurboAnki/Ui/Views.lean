import Std.Data.HashMap
import HyperVision
import TurboAnki.Core.Session
import TurboAnki.Core.Model

/-!
# Windows

Every window of the application is a pure function of the state it shows: the deck
overview of the decks, a card browser of a deck's cards, a study window of its session.
The command handler (`TurboAnki.Ui.App`) updates the state and rebuilds the window.
-/

namespace TurboAnki.Ui

open HyperVision

/-- The application's commands. Commands issued from a dialog carry what the dialog is
about, so the handler never has to guess. -/
inductive Cmd where
  /-- Bring the deck overview to the front. -/
  | showDecks
  | review
  | learn
  /-- Review if anything is due, else learn. -/
  | study
  | browse
  | newDeck
  | createDeck
  | renameDeck
  | saveDeckName (deck : DeckId)
  | deleteDeck
  | confirmDeleteDeck (deck : DeckId)
  | importWords
  | importFile (deck : DeckId)
  /-- `Enter` in a card browser: filter from the search field, else edit. -/
  | browserEnter
  | addCard
  | saveNewCard (deck : DeckId)
  | editCard
  | saveCard (card : CardId)
  | deleteCard
  | confirmDeleteCard (card : CardId)
  | resetCard
  | confirmResetCard (card : CardId)
  | reveal
  | rate (r : Rating)
  /-- Grade the typed answer, or move on after a wrong one. -/
  | check
  | endSession
  | about
deriving BEq, Repr, Inhabited

/-! ## Layout helpers -/

/-- `n` right-aligned in `width` columns. -/
def padLeft (s : String) (width : Nat) : String := "".pushn ' ' (width - s.length) ++ s

/-- The first line of a text, for one-line lists. -/
def firstLine (s : String) : String :=
  match s.splitOn "\n" with
  | [l] => l
  | l :: _ => l ++ " …"
  | [] => ""

/-- Centers every line of a text in a static text control. -/
def centered (s : String) : String := "\n".intercalate ((s.splitOn "\n").map ("^C" ++ ·))

/-- A rectangle of size `w × h` centered on the desktop, shrunk to fit it. -/
def centeredRect (desk : Rect) (w h : Nat) : Rect :=
  let w := min w desk.w
  let h := min h desk.h
  ⟨desk.x + ((desk.w - w) / 2 : Nat), desk.y + ((desk.h - h) / 2 : Nat), w, h⟩

/-- Buttons stacked along the right edge, following it when the window grows. -/
def sideButtons (iw : Nat) (buttons : List (String × Command Cmd × Bool)) : Array (Control Cmd) :=
  (buttons.zipIdx.map fun ((title, cmd, dflt), i) =>
    Control.button (iw - 14 : Nat) (1 + 2 * i : Nat) 13 title cmd (isDefault := dflt)
      (grow := { loX := true, hiX := true })).toArray

/-- Colors for messages on the gray window background. -/
def okAttr : Attr := ⟨.green, .lightGray⟩
def typoAttr : Attr := ⟨.blue, .lightGray⟩
def errorAttr : Attr := ⟨.red, .lightGray⟩
def promptAttr : Attr := ⟨.black, .lightGray⟩

/-! ## The deck overview -/

def deckColumns (width : Nat) : Nat × String :=
  let nameW := width - 31
  (nameW, fitString "Deck" nameW ++ " " ++ fitString "Kind" 10 ++ padLeft "Due" 6 ++
    padLeft "New" 6 ++ padLeft "Total" 7)

def deckRow (width : Nat) (deck : Deck) (s : DeckStats) : String :=
  let (nameW, _) := deckColumns width
  fitString deck.name nameW ++ " " ++ fitString deck.kind.label 10 ++ padLeft (toString s.due) 6 ++
    padLeft (toString s.new) 6 ++ padLeft (toString s.total) 7

/-- The overview: every deck with its counts, and what can be done with the selected one. -/
def deckWindow (bounds : Rect) (rows : Array (Deck × DeckStats)) (focused : Nat := 0) : Window Cmd :=
  let iw := bounds.w - 2
  let ih := bounds.h - 2
  let listW := iw - 17
  let textW := listW - 3
  { title := "Decks", bounds, style := .gray, flags := { close := false }, minSize := ⟨50, 18⟩
    controls := #[
      Control.staticText ⟨2, 0, textW, 1⟩ (deckColumns textW).2,
      Control.listBox "decks" ⟨1, 1, listW, ih - 2⟩ (rows.map fun (d, s) => deckRow textW d s)
        focused (grow := .stretch),
      Control.staticText ⟨1, (ih - 1 : Nat), listW, 1⟩
        "Enter studies the deck: due cards first, then new ones." (grow := .anchorBottom)
    ] ++ sideButtons iw [
      ("~S~tudy", .user .study, true),
      ("~R~eview", .user .review, false),
      ("~L~earn new", .user .learn, false),
      ("~C~ards…", .user .browse, false),
      ("~N~ew deck…", .user .newDeck, false),
      ("Rena~m~e…", .user .renameDeck, false),
      ("~D~elete…", .user .deleteDeck, false),
      ("~I~mport…", .user .importWords, false)]
    focus := some 1 }

/-! ## Card browser -/

/-- When a card is due, as the browser shows it. -/
def dueText (c : Card) (now : Instant) : String :=
  match c.sched with
  | .new => "new"
  | .seen s => if s.due ≤ now then "due" else formatSpan (s.due.ms - now.ms)

def cardRow (width : Nat) (now : Instant) (c : Card) : String :=
  let fw := (width - 8) / 2
  let bw := width - 8 - fw
  fitString (firstLine c.front) (fw - 1) ++ " " ++ fitString (firstLine c.back) (bw - 1) ++ " " ++
    padLeft (dueText c now) 6

def cardHeader (width : Nat) (deck : Deck) : String :=
  let fw := (width - 8) / 2
  let bw := width - 8 - fw
  let (f, b) := match deck.kind with
    | .dictionary => ("Word (typed)", "Translation (shown)")
    | .flashcards => ("Front", "Back")
  fitString f (fw - 1) ++ " " ++ fitString b (bw - 1) ++ " " ++ padLeft "Due" 6

/-- A deck's cards, filtered by a search, with buttons to change them. -/
def browserWindow (bounds : Rect) (deck : Deck) (cards : Array Card) (query : String) (now : Instant)
    (focused : Nat := 0) : Window Cmd :=
  let iw := bounds.w - 2
  let ih := bounds.h - 2
  let listW := iw - 17
  let textW := listW - 3
  { title := s!"Cards: {deck.name}", bounds, style := .gray, minSize := ⟨50, 14⟩
    controls := #[
      Control.label 1 0 "~F~ind" (some "query"),
      Control.inputLine "query" 8 0 (listW - 7) query (grow := .stretchX),
      Control.staticText ⟨2, 1, textW, 1⟩ (cardHeader textW deck) (grow := .stretchX),
      Control.listBox "cards" ⟨1, 2, listW, ih - 3⟩ (cards.map (cardRow textW now)) focused
        (grow := .stretch),
      Control.staticText ⟨1, (ih - 1 : Nat), listW, 1⟩
        s!"{cards.size} card(s). Enter in Find filters; Enter in the list edits." (grow := .anchorBottom)
    ] ++ sideButtons iw [
      ("~E~dit…", .user .browserEnter, true),
      ("~A~dd…", .user .addCard, false),
      ("~D~elete…", .user .deleteCard, false),
      ("~R~eset…", .user .resetCard, false),
      ("Close", .close, false)]
    focus := some 3 }

/-! ## Dialogs -/

/-- A modal question with a button that does it and one that does not. -/
def confirmDialog (desk : Rect) (title text yes : String) (cmd : Cmd) : Window Cmd :=
  let lines := text.splitOn "\n"
  let w := max 44 (lines.foldl (fun m l => max m l.length) 0 + 6)
  let h := lines.length + 7
  { Window.dialog title (centeredRect desk w h) #[
      Control.staticText ⟨2, 1, w - 6, lines.length⟩ text,
      Control.button ((w - 2) / 2 - 14 : Nat) (h - 5 : Nat) 13 yes (.user cmd),
      Control.button ((w - 2) / 2 + 1 : Nat) (h - 5 : Nat) 13 "Cancel" .cancel (isDefault := true)]
    -- Enter must not destroy anything: the focus starts on Cancel.
    with modal := true, focus := some 2 }

/-- The dialog that names a deck: a new one (with its kind), or a renamed one. -/
def deckNameDialog (desk : Rect) (title : String) (name : String) (askKind : Bool) (ok : Cmd)
    (error : String := "") : Window Cmd :=
  let h := if askKind then 14 else 10
  { Window.dialog title (centeredRect desk 56 h) (#[
      Control.label 1 1 "~N~ame" (some "name"),
      Control.inputLine "name" 9 1 42 name] ++
      (if askKind then #[
        Control.label 1 3 "~K~ind" (some "kind"),
        Control.radioButtons "kind" ⟨9, 3, 42, 2⟩
          #["~F~lashcards: show, then rate 1–4", "~D~ictionary: type, three passes"]] else #[]) ++ #[
      Control.staticText ⟨2, (h - 7 : Nat), 50, 1⟩ error (attr := some errorAttr),
      Control.button 13 (h - 5 : Nat) 13 "O~K~" (.user ok) (isDefault := true),
      Control.button 28 (h - 5 : Nat) 13 "Cancel" .cancel])
    with modal := true }

/-- Adds or edits a card. Flashcards get multi-line fields; a dictionary entry is a word
and its translation. -/
def cardDialog (desk : Rect) (deck : Deck) (title : String) (front back : String) (ok : Cmd)
    (status : String := "") (statusAttr : Attr := errorAttr) : Window Cmd :=
  match deck.kind with
  | .dictionary =>
    { Window.dialog title (centeredRect desk 62 13) #[
        Control.label 1 1 "~W~ord — what you type" (some "front"),
        Control.inputLine "front" 2 2 54 front,
        Control.label 1 4 "~T~ranslation — what you are shown" (some "back"),
        Control.inputLine "back" 2 5 54 back,
        Control.staticText ⟨2, 7, 54, 1⟩ status (attr := some statusAttr),
        Control.button 16 8 13 "~S~ave" (.user ok) (isDefault := true),
        Control.button 31 8 13 "Cancel" .cancel]
      with modal := true }
  | .flashcards =>
    { Window.dialog title (centeredRect desk 66 19) #[
        Control.label 1 1 "~F~ront" (some "front"),
        Control.memo "front" ⟨2, 2, 58, 5⟩ front,
        Control.label 1 8 "~B~ack" (some "back"),
        Control.memo "back" ⟨2, 9, 58, 4⟩ back,
        Control.staticText ⟨2, 13, 58, 1⟩ status (attr := some statusAttr),
        Control.button 18 14 13 "~S~ave" (.user ok) (isDefault := true),
        Control.button 33 14 13 "Cancel" .cancel]
      with modal := true }

/-! ## Studying flashcards -/

/-- A flashcard session: the cards (kept current as they are reviewed), the queue, and
whether the answer is showing. -/
structure StudyView where
  deck : Deck
  cards : Std.HashMap CardId Card
  study : Study CardId
  revealed : Bool := false
  /-- Answers given, by rating (`again`, `hard`, `good`, `easy`). -/
  tally : Array Nat := #[0, 0, 0, 0]

def StudyView.current? (v : StudyView) : Option Card := v.study.current? >>= (v.cards[·]?)

def tallyText (t : Array Nat) : String :=
  s!"Again {t[0]?.getD 0}  Hard {t[1]?.getD 0}  Good {t[2]?.getD 0}  Easy {t[3]?.getD 0}"

/-- The study window: the front, then the back and four rating buttons that show when the
card would come back. -/
def studyWindow (bounds : Rect) (v : StudyView) (now : Instant) : Window Cmd :=
  let iw := bounds.w - 2
  let ih := bounds.h - 2
  let textW := iw - 4
  let card := v.current?
  let front := (card.map (·.front)).getD ""
  let back := (card.map (·.back)).getD ""
  let progress := s!"{v.study.pending.length} to go · {tallyText v.tally}"
  let faceH := (ih - 6) / 2
  let base : Array (Control Cmd) := #[
    Control.staticText ⟨2, 0, textW, 1⟩ progress,
    Control.staticText ⟨2, 2, textW, faceH⟩ (centered front) (attr := some promptAttr),
    Control.staticText ⟨2, (2 + faceH : Nat), textW, 1⟩ ("".pushn '─' textW),
    Control.staticText ⟨2, (3 + faceH : Nat), textW, faceH⟩ (if v.revealed then centered back else "")]
  let buttonY : Nat := ih - 2
  let endButton := Control.button (iw - 12 : Nat) buttonY 11 "~E~nd" (.user .endSession)
  let (buttons, focus) : Array (Control Cmd) × Nat :=
    if v.revealed then
      let span (r : Rating) : String :=
        match card with
        | some c => formatSpan ((Fsrs.next c.sched now r).due.ms - now.ms)
        | none => ""
      let bw := (iw - 14) / 4
      (Rating.all.toArray.mapIdx fun i r =>
        Control.button (1 + i * bw : Nat) buttonY bw s!"~{r.toNat}~ {r.label} {span r}" (.user (.rate r))
          (isDefault := r == .good),
       base.size + 2)
    else
      (#[Control.button 1 buttonY 22 "~S~how answer" (.user .reveal) (isDefault := true)], base.size)
  { title := s!"Study: {v.deck.name}", bounds, style := .gray,
    flags := { close := false, grow := false, zoom := false },
    controls := base ++ buttons.push endButton, focus := some focus }

/-! ## Drilling a dictionary -/

/-- What the last answer earned: a typo's right spelling, shown under the next prompt,
or a wrong answer's word, shown until `Enter`. Correct answers have none. -/
structure Feedback where
  grade : Grade
  prompt : String
  expected : String
  typed : String

/-- A typing drill: the cards, the three-pass queue, and the last answer's feedback.
After a wrong answer the drill waits for `Enter` with the right answer showing. -/
structure DrillView where
  deck : Deck
  cards : Std.HashMap CardId Card
  drill : Drill CardId
  feedback : Option Feedback := none
  waiting : Bool := false

def DrillView.current? (v : DrillView) : Option Card := v.drill.current? >>= (v.cards[·]?)

/-- How a drill's first answers went: good, typo, missed. -/
def DrillView.counts (v : DrillView) : Nat × Nat × Nat :=
  let rs := v.drill.firstRatings.map (·.2)
  (rs.count .good, rs.count .hard, rs.count .again)

def feedbackText (f : Feedback) : String × Attr :=
  match f.grade with
  | .correct => ("", okAttr)
  | .typo => (s!"≈ {f.expected}    (you typed “{f.typed}”)", typoAttr)
  | .wrong => (s!"✗ {f.prompt} → {f.expected}\nPress Enter to continue.", errorAttr)

/-- The drill window: the translation, a field to type the word in, and what the previous
answer earned. -/
def drillWindow (bounds : Rect) (v : DrillView) : Window Cmd :=
  let iw := bounds.w - 2
  let ih := bounds.h - 2
  let textW := iw - 4
  let (good, typo, missed) := v.counts
  let progress :=
    s!"Pass {min v.drill.pass Drill.passes} of {Drill.passes} · {v.drill.pending.length} to go · " ++
    s!"✓ {good}  ≈ {typo}  ✗ {missed}"
  let prompt := if v.waiting then "" else ((v.current?.map (·.back)).getD "")
  let (fb, fbAttr) := (v.feedback.map feedbackText).getD ("", okAttr)
  let buttonY : Nat := ih - 2
  { title := s!"Drill: {v.deck.name}", bounds, style := .gray,
    flags := { close := false, grow := false, zoom := false },
    controls := #[
      Control.staticText ⟨2, 0, textW, 1⟩ progress,
      Control.staticText ⟨2, 2, textW, 3⟩ (centered prompt) (attr := some promptAttr),
      Control.label 1 6 "~A~nswer" (some "answer"),
      Control.inputLine "answer" 10 6 (iw - 13),
      Control.staticText ⟨2, 8, textW, 3⟩ fb (attr := some fbAttr),
      Control.button 1 buttonY 14 (if v.waiting then "~C~ontinue" else "~C~heck") (.user .check)
        (isDefault := true),
      Control.button (iw - 12 : Nat) buttonY 11 "~E~nd" (.user .endSession)]
    focus := some 3 }

end TurboAnki.Ui
