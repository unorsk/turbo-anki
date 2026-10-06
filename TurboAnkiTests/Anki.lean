import TurboAnki

/-! # Anki import: unit tests (shapes taken from a real collection) -/

namespace TurboAnkiTests

open TurboAnki TurboAnki.AnkiImport

#guard Html.toText "<div><div><span style=\"color: #24292e;\">a close friend</span></div></div>" == "a close friend"
#guard Html.toText "<ol><li> Govern</li><li>Identify</li><li>Protect</li></ol>" == "1. Govern\n2. Identify\n3. Protect"
#guard Html.toText "Risks:<ul><li><b>Strategic</b></li><li>Operational</li></ul>" == "Risks:\n- Strategic\n- Operational"
#guard Html.toText "line one<br>line two<br/><br>line three" == "line one\nline two\n\nline three"
#guard Html.toText "it&#x27;s&nbsp;fine &amp; &lt;ok&gt; &#39;x&#39;" == "it's fine & <ok> 'x'"
#guard Html.toText "R&D & more; a&b" == "R&D & more; a&b"
#guard Html.toText "  plaster  " == "plaster"

#guard deckName "Default\x1fCybersecurity\x1fGRC" == "Default::Cybersecurity::GRC"
#guard deckName "Español" == "Español"

#guard (frontBack "plaster\x1fel yeso" 0).toOption == some { front := "plaster", back := "el yeso" }
#guard (frontBack "plaster\x1fel yeso" 1).toOption == some { front := "el yeso", back := "plaster" }
#guard (frontBack "{{c1::Paris}} is the capital\x1f" 0).toOption == none
#guard (frontBack "front\x1f<div></div>" 0).toOption == none
#guard (frontBack "a\x1fb\x1fc" 2).toOption == none
#guard hasCloze "x {{c12::y}}" && !hasCloze "{{cat}} :: dog"

end TurboAnkiTests
