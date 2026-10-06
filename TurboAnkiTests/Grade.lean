import TurboAnki

/-!
# Grading: unit tests

melk's own test cases (`cli/drill.test.ts`), checked at compile time, and a few for
the Unicode handling the port had to supply itself.
-/

namespace TurboAnkiTests

open TurboAnki

-- melk's cases.
#guard grade "hund" "hund" == .correct
#guard grade "HUND" "hund" == .correct
#guard grade "de hond!" "dehond" == .correct
#guard grade "Cafe" "café" == .typo
#guard grade "far" "får" == .typo
#guard grade "har" "hår" == .typo
#guard grade "får" "får" == .correct
#guard grade "hnud" "hund" == .typo
#guard grade "hunde" "hund" == .typo
#guard grade "katze" "hund" == .wrong
#guard grade "ost" "ku" == .wrong
#guard grade "ku" "ky" == .typo
#guard grade "bibliotk" "bibliotek" == .typo
#guard grade "" "hund" == .wrong
#guard grade "  " "hund" == .wrong

-- Composed and decomposed accents are the same text; capitals outside ASCII lowercase.
#guard grade "får" "får" == .correct
#guard grade "FÅR" "får" == .correct
#guard grade "ØL" "øl" == .correct
#guard grade "ПРИВЕТ" "привет" == .correct
-- ø and æ are letters, not accented o and a.
#guard grade "ol" "øl" == .typo
#guard grade "Ærlig talt" "ærlig, talt!" == .correct
-- Unicode punctuation and spaces are ignored, as by melk's `[\p{P}\s]`.
#guard grade "«hei» — du…" "hei du" == .correct
#guard grade "a b" "ab" == .correct

-- Edit distance: a swap is one edit; the distance is symmetric.
#guard Distance.osa "hnud".toList "hund".toList == 1
#guard Distance.osa "ca".toList "abc".toList == 3
#guard Distance.osa "kitten".toList "sitting".toList == 3
#guard Distance.osa "sitting".toList "kitten".toList == 3
#guard Distance.osa [] "abc".toList == 3

-- Word files.
#guard Pair.parse? "hund ## dog" == some { front := "hund", back := "dog" }
#guard Pair.parse? "katt\tcat" == some { front := "katt", back := "cat" }
#guard Pair.parse? "   " == none
#guard Pair.parse? "a##b##c" == none
#guard Pair.parse? "##b" == none

-- Spans.
#guard formatSpan 45_000 == "45s"
#guard formatSpan (10 * 60_000) == "10m"
#guard formatSpan (3 * 86_400_000) == "3d"
#guard formatSpan (45 * 86_400_000) == "1.5mo"
#guard formatSpan (730 * 86_400_000) == "2y"

end TurboAnkiTests
