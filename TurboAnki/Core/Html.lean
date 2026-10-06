/-!
# HTML to text

Anki keeps card fields as HTML. Cards here are plain text (Markdown later), so imported
fields are flattened: block elements and `<br>` become line breaks, list items become
`- ` lines (`1. ` in numbered lists), every other tag is dropped, character references
are decoded, white space collapses as in a browser, and blank runs are tidied up.
-/

namespace TurboAnki.Html

/-- The text of a character reference without its `&` and `;` (`nbsp`, `#39`, `#x27`). -/
def decodeEntity (name : String) : Option String :=
  let named := [("nbsp", " "), ("amp", "&"), ("lt", "<"), ("gt", ">"), ("quot", "\""),
    ("apos", "'"), ("ndash", "–"), ("mdash", "—"), ("hellip", "…"), ("laquo", "«"),
    ("raquo", "»"), ("shy", "")]
  match named.lookup name with
  | some s => some s
  | none =>
    let num := if name.startsWith "#x" || name.startsWith "#X" then
        (name.drop 2).toString.toList.foldlM (fun (n : Nat) c =>
          if c.isDigit then some (n * 16 + (c.toNat - '0'.toNat))
          else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then some (n * 16 + (c.toLower.toNat - 'a'.toNat + 10))
          else none) 0
      else if name.startsWith "#" then (name.drop 1).toString.toNat?
      else none
    num.bind fun n => if n.isValidChar && n != 0 then some (String.singleton (Char.ofNat n)) else none

/-- A tag's name, lowercased, and whether it is a closing tag (`</li>`). -/
def tagName (body : String) : String × Bool :=
  let body := body.trimAscii.toString
  let closing := body.startsWith "/"
  let rest := if closing then (body.drop 1).toString else body
  ((String.ofList (rest.toList.takeWhile fun c => c.isAlphanum)).toLower, closing)

private def blockTags : List String :=
  ["div", "p", "br", "ul", "ol", "li", "tr", "h1", "h2", "h3", "h4", "h5", "h6", "blockquote", "pre",
   "hr", "table"]

/-- Tidies the result: trims each line, drops leading and trailing blank lines, and
collapses runs of blank lines to one. -/
def tidy (s : String) : String :=
  let lines := (s.splitOn "\n").map fun l => l.trimAscii.toString
  let (out, _) := lines.foldl (init := (#[], true)) fun (out, prevBlank) l =>
    if l.isEmpty then (if prevBlank then (out, true) else (out.push l, true))
    else (out.push l, false)
  let out := if out.back? == some "" then out.pop else out
  "\n".intercalate out.toList

/-- Starts a new line, unless the text is already at the start of one. -/
def newline (out : String) : String :=
  if out.isEmpty || out.back == '\n' then out else out.push '\n'

/-- Appends text as a browser shows it: runs of spaces collapse to one, and lines do not
start with spaces. -/
def emit (out : String) (s : String) : String :=
  s.foldl (init := out) fun out c =>
    let c := if c == '\t' then ' ' else c
    if c == ' ' && (out.isEmpty || out.back == ' ' || out.back == '\n') then out else out.push c

/-- The text of an HTML fragment. -/
def toText (html : String) : String := Id.run do
  let mut out := ""
  -- One counter per open list: `none` for a bulleted one, the next number for a numbered one.
  let mut lists : List (Option Nat) := []
  let mut cs := html.toList
  while !cs.isEmpty do
    match cs with
    | '<' :: rest =>
      let body := rest.takeWhile (· != '>')
      cs := (rest.dropWhile (· != '>')).drop 1
      let (name, closing) := tagName (String.ofList body)
      if name == "ol" && !closing then lists := some 1 :: lists
      else if name == "ul" && !closing then lists := none :: lists
      else if (name == "ol" || name == "ul") && closing then lists := lists.drop 1
      if name == "li" && !closing then
        match lists with
        | some n :: more =>
          out := emit (newline out) s!"{n}. "
          lists := some (n + 1) :: more
        | _ => out := emit (newline out) "- "
      -- `<br>` always breaks the line; other blocks only end the line they are on.
      else if name == "br" then out := out.push '\n'
      else if blockTags.contains name then out := newline out
    | '&' :: rest =>
      let name := rest.takeWhile fun c => c != ';' && c != '&' && c != '<' && !c.isWhitespace
      match rest.drop name.length, decodeEntity (String.ofList name) with
      | ';' :: after, some text =>
        out := emit out text
        cs := after
      | _, _ =>
        out := out.push '&'
        cs := rest
    | '\r' :: rest => cs := rest
    | c :: rest =>
      out := emit out (String.singleton c)
      cs := rest
    | [] => pure ()
  return tidy out

end TurboAnki.Html
