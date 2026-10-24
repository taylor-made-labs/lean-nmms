/-
  nmms-lean: the verified NMMS decision procedure as a command-line program.

  "derivable" means derivable in NMMS (Hlobil and Brandom 2025, ch. 3) from
  the supplied base and nothing else: the axioms are the base's atomic
  sequents. Containment is not added, so over a base without `p |~ p` the
  answer for `p ⇒ p` is false; a caller who wants Containment supplies it,
  for instance as a MONOTONE entry `a |~ a` for each atom `a`.

  Reads JSON Lines on standard input, one query per line, and writes one JSON
  result per line. A query:

    { "id": <any>,
      "base": <pyNMMS MaterialBase.to_dict() output>,
      "antecedent": [F, ...], "consequent": [F, ...],
      "cert": C,                        -- optional
    "engine": "backtracking" }         -- optional; default is the fast search

  F is a formula tree, an object with exactly one key: {"atom": "p"} (a
  string) | {"neg": F} | {"conj": [F, F]} | {"disj": [F, F]} |
  {"impl": [F, F]}; anything else, an object with a further key included, is
  refused. Formulas arrive as trees, not pyNMMS sentence strings, so that
  pyNMMS's parser stays outside what is compared; the harness builds each
  tree from pyNMMS's own parse.

  The base's "language" (pyNMMS's L_B), when present, must contain every atom
  of the base's entries and of the query: the base relation is a relation on
  sets of atoms of L_B, and a sentence with another atom is not a sentence of
  the language, so such a query is refused with an error rather than
  answered. Without "language" the language is taken to be whatever atoms
  occur. A base that lists the same pair (as sets) twice is refused, since
  pyNMMS keeps one policy per pair and the two readings could differ.

  An entry's "robustness" is read as pyNMMS 0.15.1's `Robustness.from_json`
  reads it: absent or null is EXACT; a string is a kind ("guarded" alone has
  no defeaters and matches as MONOTONE); an object has "kind" (default
  "exact") and "unless" (absent or null: no defeaters; otherwise an object
  whose "antecedent", "consequent" and "pairs" are type-checked for every
  kind). As in pyNMMS, an exclusion pair with both sides empty is refused,
  and so are defeaters on an EXACT or MONOTONE entry, an object with no
  "kind" included. nmms-lean accepts no robustness value that pyNMMS refuses
  and reads every value both accept the same way. It refuses a few that
  pyNMMS reads leniently: an "unless" of false, a zero number, "" or [] and
  "pairs" of {} or "" (pyNMMS: no defeaters); where a list of atoms is
  expected (the "antecedent" and "consequent" of "unless" or of a pair), a
  string (pyNMMS: its characters) or an object (pyNMMS: its keys); and a
  defeater that is a number, a boolean or null.

  Before parsing, a line is refused if one of its JSON strings has an
  unpaired UTF-16 surrogate escape: a `\uD800`..`\uDBFF` escape not
  immediately followed by a `\uDC00`..`\uDFFF` escape, or a `\uDC00`..`\uDFFF`
  escape on its own (hex digits in either case). `Json.parse` turns each such
  escape into U+FFFD, so distinct names such as "\udc80" and "\udc81" would
  become one atom and the answer would be about another base or sequent. A
  surrogate pair is one character and is accepted.

  C is a certificate: {"ax": true} | {"side": "L"|"R", "principal": F,
  "keep": bool (optional, default false), "premises": [C] or [C, C, C]}.
  Nothing else is a certificate node: "ax" with another value or beside
  another key, another "side", or an unknown key is refused.
  An "ax" leaf must be an atomic sequent in the base. "keep": true selects the
  book's rule instance whose context still contains the principal sentence
  (in the book `Γ, A` is `Γ ∪ {A}`, so `Γ` may contain `A`).

  The result: {"id": ..., "derivable": bool, "cert_ok": bool or null,
  "refute_ok": bool or null, "refute_len": n or null} or
  {"id": ..., "error": "..."}. "derivable" comes from `NMMS.fastProve`, the
  non-backtracking search, which `NMMS.fastProve_iff` proves equal to
  derivability (with "engine": "backtracking", from `NMMS.prove`, proved
  equal by `NMMS.prove_iff`; both together: `NMMS.reasoner_correct`);
  "cert_ok" comes from `NMMS.check`, which `NMMS.check_sound` proves sound and
  `NMMS.check_complete` complete. For an underivable sequent the program also
  builds a one-branch refutation (`NMMS.findRefute`, which returns only
  refutations `NMMS.refute` accepts, `NMMS.findRefute_sound`, and returns one
  on every underivable sequent, `NMMS.findRefute_complete`) and checks it with
  `NMMS.refute`, which `NMMS.refute_sound` proves sound: "refute_ok" is that
  check's result, `true` exactly on the underivable sequents
  (`NMMS.refuteOk_iff`), and "refute_len" the branch length.

  A query with "op": "closure" asks whether a claim is in the closure of
  initial premises under chained single-conclusion NMMS steps (`NMMS.Closure`,
  `LeanNmms/Derivation.lean`). That is a further calculation, not NMMS
  derivability (NMMS has no Cut), so its answer is "in_closure", never
  "derivable":

    { "op": "closure", "id": <any>, "request_hash": H,
      "base": <pyNMMS base>, "initial_premises": [F, ...], "claim": F,
      "certificate": { "kind": "derivation",
                       "steps": [{"premises": [F, ...], "conclusion": F, "cert": C}, ...] }
                   | { "kind": "closure-refutation", "steps": [...], "closure": ["atom", ...] } }

  H must be the lowercase hex SHA-256 of the canonical JSON (`LeanNmms/Wire.lean`)
  of {"op", "base", "initial_premises", "claim"}; the checker recomputes it and
  refuses a mismatch. The certificate is deliberately outside the hash, so a
  changed certificate is judged by the checker, not by a checksum. The answer:
  {"id", "request_hash" (echoed), "accepted": bool, "in_closure": bool or null,
  "reason" (when not accepted)}. "accepted" is `NMMS.checkDerivation` (proved
  sound by `NMMS.checkDerivation_sound`) or `NMMS.checkRefutation` (proved
  sound by `NMMS.checkRefutation_sound`); "in_closure" is true for an accepted
  derivation, false for an accepted refutation, and null when the certificate
  is refused (the checker then does not claim either answer).

  A query with "op": "score" checks a score certificate from an external library;
  see `LeanNmms/Score.lean`.
-/
import Lean.Data.Json
import LeanNmms
import LeanNmms.Wire

open Lean NMMS

def strList (j : Json) : Except String (List String) := do
  let arr ← j.getArr?
  arr.toList.mapM (fun x => x.getStr?)

def field? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => some v
  | .error _ => none

/-- A formula is an object with exactly one key (see the header); an object
with a further key is refused, not read by one of its keys. -/
partial def parseFormula (j : Json) : Except String (Formula String) := do
  let bad (_ : Unit) : String :=
    s!"not a formula (an object with exactly one key: atom, neg, conj, disj or impl): {j.compress}"
  let .obj kvs := j | throw (bad ())
  let [(k, v)] := kvs.toList | throw (bad ())
  let bin (_ : Unit) : Except String (Formula String × Formula String) := do
    let arr ← v.getArr?
    if h : arr.size = 2 then
      return (← parseFormula arr[0], ← parseFormula arr[1])
    else throw s!"{k} needs two operands"
  match k with
  | "atom" => match v with
    | .str a => return .atom a
    | _ => throw s!"atom must be a string: {j.compress}"
  | "neg" => return .neg (← parseFormula v)
  | "conj" => let (a, b) ← bin (); return .conj a b
  | "disj" => let (a, b) ← bin (); return .disj a b
  | "impl" => let (a, b) ← bin (); return .impl a b
  | _ => throw (bad ())

def asObj (what : String) (j : Json) : Except String Json :=
  match j with
  | .obj _ => pure j
  | _ => throw s!"{what} must be an object"

/-- An optional list-of-strings field: absent means empty, wrong type is an error. -/
def optStrList (j : Json) (k : String) : Except String (List String) :=
  match field? j k with
  | some v => strList v
  | none => pure []

/-- pyNMMS's `Robustness.from_json` with its `exclusion` and `__post_init__`
checks (see the header): "unless" is read and type-checked for every kind,
an exclusion pair needs an atom, and only a GUARDED entry may have defeaters. -/
def parseRobustness (j? : Option Json) : Except String (Robustness String) := do
  let (kind, unless?) ← match j? with
    | none | some Json.null => pure ("exact", none)
    | some (.str s) => pure (s, none)
    | some j@(.obj _) =>
      let kind ← match field? j "kind" with
        | some (.str k) => pure k
        | some _ => throw "robustness kind must be a string"
        | none => pure "exact"
      pure (kind, field? j "unless")
    | some _ => throw "robustness must be a string or an object"
  let u ← match unless? with
    | none | some Json.null => pure (Json.mkObj [])
    | some v => asObj "unless" v
  let left ← optStrList u "antecedent"
  let right ← optStrList u "consequent"
  let pairsJ ← match field? u "pairs" with
    | some (.arr a) => pure a.toList
    | some _ => throw "unless.pairs must be an array"
    | none => pure []
  let pairs ← pairsJ.mapM fun p => do
    let p ← asObj "unless.pairs entry" p
    let x ← optStrList p "antecedent"
    let y ← optStrList p "consequent"
    if x.isEmpty && y.isEmpty then throw "an exclusion pair needs at least one atom"
    pure (x, y)
  let defeaters := !(left.isEmpty && right.isEmpty && pairs.isEmpty)
  match kind with
  | "guarded" => return .guarded { left, right, pairs }
  | "exact" | "monotone" =>
    if defeaters then
      throw s!"defeaters (unless) are only meaningful for guarded entries, not {kind}"
    return if kind == "exact" then .exact else .monotone
  | k => throw s!"unknown robustness kind {k}"

/-- A parsed base: its entries and, when given, its language L_B. -/
structure ParsedBase where
  entries : List (Entry String)
  language : Option (List String)

/-- Every atom of a formula. -/
def formulaAtoms : Formula String → List String
  | .atom a => [a]
  | .neg A => formulaAtoms A
  | .conj A B | .disj A B | .impl A B => formulaAtoms A ++ formulaAtoms B

/-- Refuse an atom outside the base's declared language (see the header). -/
def checkLanguage (pb : ParsedBase) (what : String) (atoms : List String) :
    Except String Unit :=
  match pb.language with
  | none => pure ()
  | some L => match atoms.find? (fun a => !L.contains a) with
    | some a => throw s!"atom {a} in {what} is not in the base's language"
    | none => pure ()

def checkFormulas (pb : ParsedBase) (what : String) (fs : List (Formula String)) :
    Except String Unit :=
  checkLanguage pb what (fs.flatMap formulaAtoms)

/-- `consequences` is required (pyNMMS's `base.schema.json`) and must be an
array; `language`, when present, is a list of atom names that must contain
every atom of the entries. A pair listed twice is refused. -/
def parseBase (j : Json) : Except String ParsedBase := do
  let cs ← match field? j "consequences" with
    | some v => (do let a ← v.getArr?; pure a.toList)
    | none => throw "base needs a \"consequences\" array"
  let language ← match field? j "language" with
    | none | some Json.null => pure none
    | some v => some <$> strList v
  let entries ← cs.mapM fun e => do
    let ant ← strList (← e.getObjVal? "antecedent")
    let con ← strList (← e.getObjVal? "consequent")
    let rob ← parseRobustness (field? e "robustness")
    pure ({ ant, con, rob } : Entry String)
  let pb : ParsedBase := { entries, language }
  for e in entries do
    checkLanguage pb "the base" (e.ant ++ e.con)
    if (entries.filter fun e' => setEqB e.ant e'.ant && setEqB e.con e'.con).length > 1 then
      throw s!"the base lists the pair {repr e.ant} |~ {repr e.con} more than once"
  pure pb

/-- Number of premises the rule on `φ` (left side if `left`) has; `none` for an
atom, which is no rule at all. Matches `NMMS.check`. -/
def ruleArity (left : Bool) : Formula String → Option Nat
  | .atom _ => none
  | .neg _ => some 1
  | .impl _ _ => some (if left then 3 else 1)
  | .conj _ _ => some (if left then 1 else 3)
  | .disj _ _ => some (if left then 3 else 1)

/-- A certificate node is an axiom leaf `{"ax": true}` with no other key, or
a rule node with "side" "L" or "R", "principal", "premises" and optional
"keep"; any other object is refused (see the header). -/
partial def parseCert (j : Json) : Except String (Cert String) := do
  let .obj kvs := j | throw s!"a certificate node must be an object: {j.compress}"
  if let some v := field? j "ax" then
    if v != Json.bool true then throw s!"\"ax\" must be true, got {v.compress}"
    if kvs.keys.contains "side" then
      throw "a certificate node has \"ax\" or \"side\", not both"
    if kvs.size != 1 then
      throw s!"an \"ax\" leaf has no other keys: {j.compress}"
    return .ax
  if let some k := kvs.keys.find? (fun k => !["side", "principal", "keep", "premises"].contains k) then
    throw s!"unknown key {k} in a certificate node"
  let side ← match field? j "side" with
    | some (.str "L") => pure "L"
    | some (.str "R") => pure "R"
    | some v => throw s!"certificate side must be \"L\" or \"R\", got {v.compress}"
    | none => throw "a certificate node needs \"ax\": true or a \"side\""
  let φ ← parseFormula (← j.getObjVal? "principal")
  let keep ← match field? j "keep" with
    | none | some Json.null => pure false
    | some (Json.bool b) => pure b
    | some _ => throw "keep must be a boolean"
  let ps ← (← j.getObjVal? "premises").getArr?
  let cs ← ps.toList.mapM parseCert
  if let some n := ruleArity (side == "L") φ then
    if cs.length != n then
      throw s!"certificate node needs {n} premises, got {cs.length}"
  let c1 := cs.getD 0 .ax
  let c2 := cs.getD 1 .ax
  let c3 := cs.getD 2 .ax
  return .node (side == "L") φ keep c1 c2 c3

/-- Every formula a certificate names. -/
def certFormulas : Cert String → List (Formula String)
  | .ax => []
  | .node _ φ _ c1 c2 c3 => φ :: (certFormulas c1 ++ certFormulas c2 ++ certFormulas c3)

def parseStep (j : Json) : Except String (DerivationStep String) := do
  let ps ← (← j.getObjVal? "premises").getArr?
  let premises ← ps.toList.mapM parseFormula
  let conclusion ← parseFormula (← j.getObjVal? "conclusion")
  let cert ← parseCert (← j.getObjVal? "cert")
  pure { premises, conclusion, cert }

/-- Why a derivation was refused: the first failing step (diagnostic only; the
decision is `checkDerivation`'s). -/
def diagnoseSteps (B : List (Entry String)) :
    Nat → List (Formula String) → List (DerivationStep String) → Except String (List (Formula String))
  | _, avail, [] => pure avail
  | k, avail, s :: rest =>
    match s.premises.find? (fun p => !avail.contains p) with
    | some p => throw s!"step {k}: premise {repr p} is neither an initial premise nor concluded by an earlier step"
    | none =>
      if check (baseRel B) s.cert s.premises [s.conclusion] then
        diagnoseSteps B (k + 1) (s.conclusion :: avail) rest
      else throw s!"step {k}: its local proof does not check (premises ⇒ conclusion is not shown derivable)"

def rejectReason (B : List (Entry String)) (initial : List (Formula String))
    (steps : List (DerivationStep String)) (claim : Formula String) : String :=
  match diagnoseSteps B 0 initial steps with
  | .error e => e
  | .ok avail =>
    if avail.contains claim then "rejected"
    else "the steps check but never conclude the claim"

def refutationReason (B : List (Entry String)) (initial : List (Formula String))
    (cert : ClosureRefutation String) (claim : Formula String) : String :=
  match claim with
  | .atom c =>
    if !allAtomic initial then "closure refutations need atomic initial premises"
    else if !(atomsOf initial).all (fun a => cert.closure.contains a) then
      "the listed closure leaves out an initial premise"
    else if cert.closure.contains c then "the listed closure contains the claim"
    else match B.find? (fun e => e.firesOn cert.closure) with
      | some e => s!"not saturated: the base entry {repr e.ant} |~ {repr e.con} licenses a conclusion outside the listed closure from atoms inside it"
      | none => match diagnoseSteps B 0 initial cert.steps with
        | .error e => e
        | .ok avail =>
          match cert.closure.find? (fun a => !avail.contains (.atom a)) with
          | some a => s!"the steps never reach the listed atom {a}"
          | none => "rejected"
  | _ => "closure refutations need an atomic claim"

/-- Answer an "op": "score" query (`LeanNmms/Score.lean`). -/
def handleScore (j : Json) (id : Json) : Except String Json := NMMS.Score.handle j id

/-- Answer an "op": "closure" query (see the header). -/
def handleClosure (j : Json) (id : Json) : Except String Json := do
  let given := (field? j "request_hash").getD Json.null
  let bound := Json.mkObj [("op", Json.str "closure"),
    ("base", ← j.getObjVal? "base"), ("initial_premises", ← j.getObjVal? "initial_premises"),
    ("claim", ← j.getObjVal? "claim")]
  let expected ← NMMS.Wire.digest bound
  let reply (accepted : Bool) (inClosure : Json) (reason : Option String) : Json :=
    Json.mkObj ([("id", id), ("request_hash", given), ("accepted", Json.bool accepted),
      ("in_closure", inClosure)] ++ (match reason with
        | some r => [("reason", Json.str r)]
        | none => []))
  if given != Json.str expected then
    return reply false Json.null (some "request_hash does not match the canonical hash of op, base, initial_premises and claim")
  let pb ← parseBase (← j.getObjVal? "base")
  let B := pb.entries
  let initial ← (← (← j.getObjVal? "initial_premises").getArr?).toList.mapM parseFormula
  let claim ← parseFormula (← j.getObjVal? "claim")
  let cj ← j.getObjVal? "certificate"
  let kind ← (← cj.getObjVal? "kind").getStr?
  let steps ← (← (← cj.getObjVal? "steps").getArr?).toList.mapM parseStep
  checkFormulas pb "the initial premises" initial
  checkFormulas pb "the claim" [claim]
  checkFormulas pb "the certificate"
    (steps.flatMap fun s => s.conclusion :: s.premises ++ certFormulas s.cert)
  match kind with
  | "derivation" =>
    if checkDerivation B initial steps claim then
      return reply true (Json.bool true) none
    else return reply false Json.null (some (rejectReason B initial steps claim))
  | "closure-refutation" =>
    let closure ← strList (← cj.getObjVal? "closure")
    checkLanguage pb "the listed closure" closure
    let cert : ClosureRefutation String := { steps, closure }
    if checkRefutation B initial cert claim then
      return reply true (Json.bool false) none
    else return reply false Json.null (some (refutationReason B initial cert claim))
  | k => throw s!"unknown certificate kind {k}"

def handle (line : String) : Json :=
  match Json.parse line with
  | .error e => Json.mkObj [("error", Json.str s!"bad JSON: {e}")]
  | .ok j =>
    let id := (field? j "id").getD Json.null
    let r : Except String Json := do
      if let some op := field? j "op" then
        match op with
        | Json.str "closure" => return ← handleClosure j id
        | Json.str "score" => return ← handleScore j id
        | v => throw s!"unknown op {v.compress}"
      let pb ← parseBase (← j.getObjVal? "base")
      let Γ ← (← (← j.getObjVal? "antecedent").getArr?).toList.mapM parseFormula
      let Δ ← (← (← j.getObjVal? "consequent").getArr?).toList.mapM parseFormula
      checkFormulas pb "the sequent" (Γ ++ Δ)
      let R := baseRel pb.entries
      let backtracking ← match field? j "engine" with
        | none | some Json.null => pure false
        | some (Json.str "fast") => pure false
        | some (Json.str "backtracking") => pure true
        | some v => throw s!"unknown engine {v.compress} (expected \"fast\" or \"backtracking\")"
      let d := if backtracking then prove R Γ Δ else fastProve R Γ Δ
      let (refOk, refLen) : Json × Json :=
        if d then (Json.null, Json.null) else
        match findRefute R Γ Δ with
        | some c => (Json.bool (refute R c Γ Δ), Json.num c.length)
        | none => (Json.bool false, Json.null)
      let certOk : Json ← match field? j "cert" with
        | none => pure Json.null
        | some Json.null => pure Json.null
        | some cj => do
          let c ← parseCert cj
          checkFormulas pb "the certificate" (certFormulas c)
          pure (Json.bool (check R c Γ Δ))
      pure (Json.mkObj [("id", id), ("derivable", Json.bool d), ("cert_ok", certOk),
        ("refute_ok", refOk), ("refute_len", refLen)])
    match r with
    | .ok out => out
    | .error e => Json.mkObj [("id", id), ("error", Json.str e)]

/-- Resource limits (see the header). -/
structure Limits where
  maxLineBytes : Nat := 4194304
  maxDepth : Nat := 256

/-- The UTF-16 code unit of the escape `\uXXXX` whose backslash is at `i`
(hex digits in either case), or `none` if the bytes there are not one. -/
def unicodeEscapeAt (bytes : ByteArray) (i : Nat) : Option Nat := do
  if bytes[i]? != some 92 || bytes[i + 1]? != some 117 then none
  let digit (k : Nat) : Option Nat := do
    let b ← bytes[i + 2 + k]?
    if 48 ≤ b && b ≤ 57 then pure (b - 48).toNat
    else if 65 ≤ b && b ≤ 70 then pure (b - 55).toNat
    else if 97 ≤ b && b ≤ 102 then pure (b - 87).toNat
    else none
  return (← digit 0) * 4096 + (← digit 1) * 256 + (← digit 2) * 16 + (← digit 3)

/-- Check a raw line before `Json.parse`, without parsing it, in one pass and
constant memory; the result is the error to report, if any. Two checks:
the deepest `{`/`[` nesting (string contents and escapes are skipped),
stopping as soon as `cap` is exceeded, since `Json.parse`'s recursion would
otherwise follow the nesting; and every `\u` escape inside a string, which
must not be an unpaired UTF-16 surrogate (see the header): an escape in
D800-DBFF must be immediately followed by one in DC00-DFFF, and the pair is
consumed together. -/
def prescan (bytes : ByteArray) (cap : Nat) : Option String := Id.run do
  let unpaired (c : Nat) : String :=
    s!"unpaired UTF-16 surrogate escape \\u{(String.ofList (Nat.toDigits 16 c)).toUpper} in a JSON string"
  let mut depth := 0
  let mut inStr := false
  let mut skip := 0  -- bytes of the current escape still to pass over
  for i in [0:bytes.size] do
    if skip > 0 then
      skip := skip - 1
      continue
    let b := bytes[i]!
    if inStr then
      if b == 92 then
        match unicodeEscapeAt bytes i with
        | none => skip := 1
        | some c =>
          if c < 0xD800 || c > 0xDFFF then skip := 5
          else if c ≥ 0xDC00 then return some (unpaired c)
          else match unicodeEscapeAt bytes (i + 6) with
            | some d => if 0xDC00 ≤ d && d ≤ 0xDFFF then skip := 11 else return some (unpaired c)
            | none => return some (unpaired c)
      else if b == 34 then inStr := false
    else if b == 34 then inStr := true
    else if b == 123 || b == 91 then
      depth := depth + 1
      if depth > cap then return some s!"nesting deeper than --max-depth {cap}"
    else if b == 125 || b == 93 then
      depth := depth - 1
  return none

def errLine (msg : String) : Json := Json.mkObj [("error", Json.str msg)]

/-- Answer one complete line (already known to fit `maxLineBytes`). -/
def answerLine (lim : Limits) (bytes : ByteArray) : Option Json :=
  match String.fromUTF8? bytes with
  | none => some (errLine "line is not valid UTF-8")
  | some line =>
    let t := line.trimAscii.toString
    if t.isEmpty then none
    else if let some e := prescan t.toUTF8 lim.maxDepth then some (errLine e)
    else some (handle t)

/-- Read standard input a byte at a time (`Stream.read n` blocks until `n` bytes
or end of input, which would deadlock an interactive caller waiting for an
answer). Memory stays bounded by `maxLineBytes` even for an endless line: the
overlong line is discarded as it streams past and reported once its newline
arrives. -/
partial def loop (lim : Limits) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream)
    (buf : ByteArray) (over : Bool) : IO Unit := do
  let emit (o : Option Json) : IO Unit := do
    if let some r := o then
      stdout.putStrLn r.compress
      stdout.flush
  let chunk ← stdin.read 1
  if chunk.isEmpty then
    -- end of input: an unterminated last line still gets an answer
    if over then emit (some (errLine s!"line longer than --max-line-bytes {lim.maxLineBytes}"))
    else emit (answerLine lim buf)
    return
  let mut buf := buf
  let mut over := over
  for b in chunk do
    if b == 10 then
      if over then emit (some (errLine s!"line longer than --max-line-bytes {lim.maxLineBytes}"))
      else emit (answerLine lim buf)
      buf := ByteArray.empty
      over := false
    else if !over then
      if buf.size >= lim.maxLineBytes then
        over := true
        buf := ByteArray.empty
      else buf := buf.push b
  loop lim stdin stdout buf over

def usage : String :=
  "usage: nmms-lean [--max-line-bytes N] [--max-depth N]   (JSON Lines on stdin)"

def parseArgs (lim : Limits) : List String → Except String Limits
  | [] => pure lim
  | "--max-line-bytes" :: v :: rest =>
    match v.toNat? with
    | some n => if n == 0 then throw "--max-line-bytes must be positive"
                else parseArgs { lim with maxLineBytes := n } rest
    | none => throw s!"--max-line-bytes needs a number, got {v}"
  | "--max-depth" :: v :: rest =>
    match v.toNat? with
    | some n => if n == 0 then throw "--max-depth must be positive"
                else parseArgs { lim with maxDepth := n } rest
    | none => throw s!"--max-depth needs a number, got {v}"
  | a :: _ => throw s!"unrecognised argument {a}"

def main (args : List String) : IO UInt32 := do
  match parseArgs {} args with
  | .error e =>
    (← IO.getStderr).putStrLn s!"{e}\n{usage}"
    return 2
  | .ok lim =>
    loop lim (← IO.getStdin) (← IO.getStdout) ByteArray.empty false
    return 0
