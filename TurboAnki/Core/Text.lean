import Std.Data.HashMap
import TurboAnki.Core.UnicodeData

/-!
# Normalizing typed answers

What melk's drill does with JavaScript's Unicode support, for the scripts in
`UnicodeData`: answers are compared in composed form (NFC), lowercased, with
punctuation and white space dropped. Accents are kept, because in Norwegian `får`
and `far` are different words; `stripAccents` removes them only to tell an accent
slip from a misspelling.

Texts are handled as lists of characters, which is what the edit distance and the
proofs about grading work with.
-/

namespace TurboAnki.Text

open UnicodeData

private def decompositionMap : Std.HashMap Nat (Nat × Nat) :=
  decompositions.foldl (fun m (c, b, k) => m.insert c (b, k)) {}

private def compositionMap : Std.HashMap (Nat × Nat) Nat :=
  decompositions.foldl (fun m (c, b, k) => m.insert (b, k) c) {}

private def lowercaseMap : Std.HashMap Nat Nat :=
  lowercase.foldl (fun m (u, l) => m.insert u l) {}

private def inRanges (rs : Array (Nat × Nat)) (c : Char) : Bool :=
  rs.any fun (lo, hi) => lo ≤ c.toNat && c.toNat ≤ hi

/-- A combining diacritical mark (U+0300‥U+036F). -/
def isMark (c : Char) : Bool := 0x300 ≤ c.toNat && c.toNat ≤ 0x36F

def isPunctuation (c : Char) : Bool := inRanges punctuation c

def isSpace (c : Char) : Bool := inRanges whitespace c

/-- Full canonical decomposition of one character (bounded by its code point, which
strictly decreases along a decomposition). -/
def decomposeChar (c : Char) : List Char :=
  go 4 c
where
  go : Nat → Char → List Char
    | 0, c => [c]
    | n + 1, c =>
      match decompositionMap[c.toNat]? with
      | some (b, k) => go n (Char.ofNat b) ++ [Char.ofNat k]
      | none => [c]

/-- Canonical decomposition (NFD, for the characters in `UnicodeData`). -/
def decompose (cs : List Char) : List Char := cs.flatMap decomposeChar

/-- Canonical composition of a decomposed text: each mark is combined with the
character before it where Unicode has a composed form. -/
def compose (cs : List Char) : List Char :=
  (cs.foldl step []).reverse
where
  step : List Char → Char → List Char
    | prev :: done, c =>
      if isMark c then
        match compositionMap[(prev.toNat, c.toNat)]? with
        | some k => Char.ofNat k :: done
        | none => c :: prev :: done
      else c :: prev :: done
    | [], c => [c]

/-- Composed normal form (NFC, for the characters in `UnicodeData`). -/
def nfc (cs : List Char) : List Char := compose (decompose cs)

/-- Lowercase, for ASCII and the capitals in `UnicodeData`. -/
def toLower (c : Char) : Char :=
  if c.toNat < 128 then c.toLower
  else match lowercaseMap[c.toNat]? with
    | some l => Char.ofNat l
    | none => c

/-- What a typed answer is compared by: composed, lowercased, without punctuation and
white space (`"De hund!"` and `"dehund"` agree; `"får"` and `"far"` do not). -/
def normalize (s : String) : List Char :=
  ((nfc s.toList).map toLower).filter fun c => !isPunctuation c && !isSpace c

/-- The text without its accents (`"får"` becomes `"far"`). -/
def stripAccents (cs : List Char) : List Char :=
  (decompose cs).filter (!isMark ·)

end TurboAnki.Text
