/-
  LeanNmms.Score

  Re-deriving an external Python library's score from its certificate (a
  library of commitments, entitlements and incompatibilities over RDF
  records; it is not part of this repository). `nmms-lean` answers
  `{"op": "score", "id", "request_hash", "input", "certificate"}` with
  `checkScore`; the input and certificate formats are written by that
  library's certificate emitter.

  **What is checked, and by what.** The input is the authoritative ground
  problem (authenticated outside Lean). The certificate is untrusted. For the
  shared record and then for each party, `checkScore`:

  1. reads the claimed closure and *grounds every rule over it itself*: a
     join of the rule's premise patterns against the closure, the value guard
     re-evaluated (this module's model of pyNMMS's guard language, including
     its rule that an evaluation error makes the guard false), and every
     defeater's solutions searched for. A party's instances must use at least
     one premise outside the record's closure (attribution: only conclusions
     that use the party's own claims are the party's);
  2. checks each claimed application instance by instance: the entry exists,
     the binding binds exactly the premise variables, the ground premises and
     conclusion are the patterns under the binding, the guard holds, there is
     one defeater check per declared defeater, and the instance is one of the
     instances of step 1. It passes the application, with the layer the
     certificate claims, to the proved core `NMMS.checkGroundClosure`
     (`LeanNmms/Ground.lean`), which checks layers, order, premise
     availability, that no defeater fires on the lower layers, saturation and
     the exact closure;
  3. recomputes the open incompatibilities (and the record's background
     ones) from the exclusion entries over the closure and requires the
     certificate's lists to be the same sets;
  4. builds the entitlement nodes from the input (undertakings, challenges,
     deferrals, the record facts' sources) and the checked applications and
     incompatibilities, never from certificate flags, and checks the rounds
     with the proved core `NMMS.checkEntitlement` (`LeanNmms/Entitlement.lean`);
  5. returns the score it re-derived: each holder's commitments, entitlements
     and open incompatibilities, and the record's background incompatibilities.

  **What the theorems cover.** `checkGroundClosure_exact` and
  `checkEntitlement_sound` are proved about the ground cores. Steps 1 to 5
  around them (JSON reading, grounding by join, guard evaluation,
  attribution, node construction, the projection) are ordinary Lean code,
  compiled and tested (against that library's conformance logs, which are
  not included here), not proved. In particular the
  completeness of the grounding (that the join finds every instance whose
  premises are in the closure) is not a theorem.
-/
import Lean.Data.Json
import LeanNmms.Ground
import LeanNmms.Entitlement
import LeanNmms.Wire

namespace NMMS.Score

open Lean NMMS

/-! ### Terms, patterns, guards -/

/-- An RDF term as the library uses them: an IRI, a plain string literal, an
integer literal. -/
inductive Term where
  | iri (s : String)
  | str (s : String)
  | int (i : Int)
  deriving DecidableEq, Repr, Inhabited

abbrev Triple := Term × Term × Term

inductive PT where
  | var (n : String)
  | const (t : Term)
  deriving DecidableEq, Repr, Inhabited

structure Pat where
  s : PT
  p : PT
  o : PT
  deriving DecidableEq, Repr, Inhabited

abbrev Binding := List (String × Term)

/-- A guard literal: a term, or a Boolean (`true`/`false` in a guard). -/
inductive GLit where
  | term (t : Term)
  | bool (b : Bool)
  deriving Repr, Inhabited

/-- A comparison operand: a variable, a literal, or a function of one. -/
inductive Operand where
  | var (n : String)
  | lit (l : GLit)
  | fn (name : String) (arg : Operand)
  deriving Repr, Inhabited

inductive Guard where
  | or (a b : Guard)
  | and (a b : Guard)
  | not (a : Guard)
  | cmp (op : String) (a b : Operand)
  | inList (a : Operand) (items : List Operand)
  deriving Repr, Inhabited

/-- pyNMMS's comparable values (`pynmms.rdf.values._value`). -/
inductive Val where
  | str (s : String)
  | num (i : Int)
  | bool (b : Bool)
  | node (s : String)
  deriving DecidableEq, Repr

def xsd (local_ : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ local_

def lookupVar (b : Binding) (n : String) : Option Term := (b.find? (·.1 == n)).map (·.2)

def termVal : Term → Val
  | .iri s => .node s
  | .str s => .str s
  | .int i => .num i

def litVal : GLit → Val
  | .term t => termVal t
  | .bool b => .bool b

/-- A function of a variable or literal (`pynmms.rdf.values._fn`). -/
def applyFn (name : String) (x : GLit) : Except Unit Val :=
  match name, x with
  | "str", .term (.iri s) => pure (.str s)
  | "str", .term (.str s) => pure (.str s)
  | "str", .term (.int i) => pure (.str (toString i))
  | "str", .bool b => pure (.str (if b then "true" else "false"))
  | "isLiteral", .term (.iri _) => pure (.bool false)
  | "isLiteral", _ => pure (.bool true)
  | "isIRI", .term (.iri _) => pure (.bool true)
  | "isIRI", _ => pure (.bool false)
  | "isBlank", _ => pure (.bool false)
  | "datatype", .term (.iri _) => throw ()
  | "datatype", .term (.str _) => pure (.node (xsd "string"))
  | "datatype", .term (.int _) => pure (.node (xsd "integer"))
  | "datatype", .bool _ => pure (.node (xsd "boolean"))
  | _, _ => throw ()

def rawOperand (b : Binding) : Operand → Except Unit GLit
  | .var n => match lookupVar b n with
    | some t => pure (.term t)
    | none => throw ()
  | .lit l => pure l
  | .fn _ _ => throw ()

def evalOperand (b : Binding) : Operand → Except Unit Val
  | .var n => match lookupVar b n with
    | some t => pure (termVal t)
    | none => throw ()
  | .lit l => pure (litVal l)
  | .fn name arg => do applyFn name (← rawOperand b arg)

/-- `pynmms.rdf.values._compare`: values of different kinds compare false. -/
def compareVal (op : String) : Val → Val → Bool
  | .str a, .str b => match op with
    | "=" => a == b | "!=" => a != b | "<" => decide (a < b) | "<=" => decide (a ≤ b)
    | ">" => decide (b < a) | ">=" => decide (b ≤ a) | _ => false
  | .num a, .num b => match op with
    | "=" => a == b | "!=" => a != b | "<" => decide (a < b) | "<=" => decide (a ≤ b)
    | ">" => decide (b < a) | ">=" => decide (b ≤ a) | _ => false
  | .bool a, .bool b => match op with
    | "=" => a == b | "!=" => a != b | _ => false
  | .node a, .node b => match op with
    | "=" => a == b | "!=" => a != b | _ => false
  | _, _ => false

def anyEq (b : Binding) (v : Val) : List Operand → Except Unit Bool
  | [] => pure false
  | x :: xs => do
    if compareVal "=" v (← evalOperand b x) then pure true else anyEq b v xs

/-- Guard evaluation; an error is propagated, and the caller reads it as false. -/
def evalGuard (b : Binding) : Guard → Except Unit Bool
  | .or x y => do if (← evalGuard b x) then pure true else evalGuard b y
  | .and x y => do if (← evalGuard b x) then evalGuard b y else pure false
  | .not x => do pure !(← evalGuard b x)
  | .cmp op x y => do
    let vx ← evalOperand b x
    let vy ← evalOperand b y
    pure (compareVal op vx vy)
  | .inList x items => do anyEq b (← evalOperand b x) items

def guardHolds (g : Option Guard) (b : Binding) : Bool :=
  match g with
  | none => true
  | some e => match evalGuard b e with
    | .ok v => v
    | .error _ => false

/-! ### Matching -/

def matchPT (b : Binding) : PT → Term → Option Binding
  | .const c, t => if c == t then some b else none
  | .var n, t => match lookupVar b n with
    | some u => if u == t then some b else none
    | none => some ((n, t) :: b)

def matchPat (b : Binding) (p : Pat) (t : Triple) : Option Binding := do
  let b ← matchPT b p.s t.1
  let b ← matchPT b p.p t.2.1
  matchPT b p.o t.2.2

/-- Every extension of `b` matching all the patterns against `C`. -/
def joinAll (C : List Triple) : List Pat → Binding → List Binding
  | [], b => [b]
  | p :: ps, b => C.flatMap fun t => match matchPat b p t with
    | some b' => joinAll C ps b'
    | none => []

def applyPT (b : Binding) : PT → Option Term
  | .const c => some c
  | .var n => lookupVar b n

def applyPat (b : Binding) (p : Pat) : Option Triple := do
  pure (← applyPT b p.s, ← applyPT b p.p, ← applyPT b p.o)

def solutions (C : List Triple) (pats : List Pat) (g : Option Guard) (b : Binding) :
    List Binding :=
  (joinAll C pats b).filter (guardHolds g)

def patVars (p : Pat) : List String :=
  [p.s, p.p, p.o].filterMap fun | .var n => some n | .const _ => none

/-! ### Atom identities -/

def termKey : Term → String
  | .iri s => "I" ++ toString s.length ++ ":" ++ s
  | .str s => "S" ++ toString s.length ++ ":" ++ s
  | .int i => "N" ++ toString i ++ ";"

def tripleKey (t : Triple) : String := termKey t.1 ++ termKey t.2.1 ++ termKey t.2.2

def dedup {β : Type} [BEq β] (l : List β) : List β :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-! ### Input and certificate -/

structure Rule where
  name : String
  layer : Nat
  premises : List Pat
  guard : Option Guard
  conclusion : Option Pat
  defeaters : List (List Pat × Option Guard)
  deriving Inhabited

structure Undertaking where
  claim : Triple
  act : String
  kind : String
  to : Option String

structure HolderIn where
  name : String
  undertakings : List Undertaking

structure FactIn where
  claim : Triple
  sources : List (Option String)

structure Input where
  prefixes : List (String × String)
  rules : List Rule
  facts : List FactIn
  challenged : List String
  holders : List HolderIn

structure CertApp where
  holder : String
  entry : String
  binding : Binding
  layer : Int
  premises : List Triple
  conclusion : Option Triple
  checks : List (Nat × Bool)

structure CertEval where
  closure : List Triple
  incompat : List (String × List Triple)
  background : List (String × List Triple)

structure Cert where
  evals : List (String × CertEval)
  apps : List CertApp
  rounds : List (List (String × Triple))

/-! ### JSON reading -/

def obj? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => some v
  | .error _ => none

def getInt (j : Json) : Except String Int := do
  match j with
  | .num n => if n.exponent == 0 then pure n.mantissa else throw "expected an integer"
  | _ => throw "expected an integer"

def arr (j : Json) : Except String (List Json) := do return (← j.getArr?).toList

def parseTerm (j : Json) : Except String Term := do
  if let some v := obj? j "iri" then return .iri (← v.getStr?)
  if let some v := obj? j "str" then return .str (← v.getStr?)
  if let some v := obj? j "int" then return .int (← getInt v)
  throw s!"not a term: {j.compress}"

def parsePT (j : Json) : Except String PT := do
  if let some v := obj? j "var" then return .var (← v.getStr?)
  return .const (← parseTerm j)

def parsePat (j : Json) : Except String Pat := do
  match ← arr j with
  | [a, b, c] => return { s := ← parsePT a, p := ← parsePT b, o := ← parsePT c }
  | _ => throw "a pattern has three terms"

def parseTriple (j : Json) : Except String Triple := do
  match ← arr j with
  | [a, b, c] => return (← parseTerm a, ← parseTerm b, ← parseTerm c)
  | _ => throw "a claim has three terms"

partial def parseOperand (j : Json) : Except String Operand := do
  match ← (← j.getObjVal? "g").getStr? with
  | "var" => return .var (← (← j.getObjVal? "name").getStr?)
  | "lit" =>
    let v ← j.getObjVal? "value"
    if let some b := obj? v "bool" then return .lit (.bool (← b.getBool?))
    return .lit (.term (← parseTerm v))
  | "fn" => return .fn (← (← j.getObjVal? "fn").getStr?) (← parseOperand (← j.getObjVal? "arg"))
  | k => throw s!"unknown guard operand {k}"

partial def parseGuard (j : Json) : Except String Guard := do
  match ← (← j.getObjVal? "g").getStr? with
  | "or" => return .or (← parseGuard (← j.getObjVal? "left")) (← parseGuard (← j.getObjVal? "right"))
  | "and" => return .and (← parseGuard (← j.getObjVal? "left")) (← parseGuard (← j.getObjVal? "right"))
  | "not" => return .not (← parseGuard (← j.getObjVal? "arg"))
  | "cmp" =>
    let op ← (← j.getObjVal? "op").getStr?
    unless ["<", "<=", ">", ">=", "=", "!="].contains op do throw s!"unknown comparison {op}"
    return .cmp op (← parseOperand (← j.getObjVal? "left")) (← parseOperand (← j.getObjVal? "right"))
  | "in" =>
    let left ← parseOperand (← j.getObjVal? "left")
    let items ← (← arr (← j.getObjVal? "items")).mapM parseOperand
    return .inList left items
  | k => throw s!"unknown guard node {k}"

def parseOptGuard (j : Json) : Except String (Option Guard) :=
  match j with
  | .null => pure none
  | g => some <$> parseGuard g

def parseRule (j : Json) : Except String Rule := do
  let layer ← getInt (← j.getObjVal? "layer")
  if layer < 0 then throw "a negative layer"
  let conclusion ← match ← j.getObjVal? "conclusion" with
    | .null => pure none
    | c => some <$> parsePat c
  let defeaters ← (← arr (← j.getObjVal? "defeaters")).mapM fun d => do
    pure ((← (← arr (← d.getObjVal? "patterns")).mapM parsePat), ← parseOptGuard (← d.getObjVal? "guard"))
  return { name := ← (← j.getObjVal? "name").getStr?, layer := layer.toNat,
           premises := ← (← arr (← j.getObjVal? "premises")).mapM parsePat,
           guard := ← parseOptGuard (← j.getObjVal? "guard"), conclusion, defeaters }

def optStr (j : Json) : Except String (Option String) :=
  match j with
  | .null => pure none
  | v => some <$> v.getStr?

def parseInput (j : Json) : Except String Input := do
  let prefixes ← (← arr (← j.getObjVal? "prefixes")).mapM fun p => do
    match ← arr p with
    | [a, b] => pure (← a.getStr?, ← b.getStr?)
    | _ => throw "a prefix is [name, namespace]"
  let rules ← (← arr (← j.getObjVal? "rules")).mapM parseRule
  let facts ← (← arr (← j.getObjVal? "facts")).mapM fun f => do
    pure { claim := ← parseTriple (← f.getObjVal? "claim"),
           sources := ← (← arr (← f.getObjVal? "sources")).mapM optStr : FactIn }
  let challenged ← (← arr (← j.getObjVal? "challenged")).mapM (·.getStr?)
  let holders ← (← arr (← j.getObjVal? "holders")).mapM fun h => do
    let us ← (← arr (← h.getObjVal? "undertakings")).mapM fun u => do
      pure { claim := ← parseTriple (← u.getObjVal? "claim"), act := ← (← u.getObjVal? "act").getStr?,
             kind := ← (← u.getObjVal? "kind").getStr?, to := ← optStr ((obj? u "to").getD .null) : Undertaking }
    pure { name := ← (← h.getObjVal? "holder").getStr?, undertakings := us : HolderIn }
  return { prefixes, rules, facts, challenged, holders }

/-- A compact name `prefix:local` back to its IRI. -/
def expand (prefixes : List (String × String)) (s : String) : Except String Term := do
  match s.splitOn ":" with
  | p :: rest@(_ :: _) =>
    match prefixes.find? (·.1 == p) with
    | some (_, ns) => pure (.iri (ns ++ ":".intercalate rest))
    | none => throw s!"unknown prefix in {s}"
  | _ => throw s!"{s} is not a compact name"

def parseCompact (prefixes : List (String × String)) (j : Json) : Except String Term := do
  match j with
  | .str s => expand prefixes s
  | .num _ => return .int (← getInt j)
  | _ =>
    let v ← j.getObjVal? "lit"
    match v with
    | .str s => pure (.str s)
    | .num _ => return .int (← getInt v)
    | _ => throw "a literal is a string or an integer"

def parseCompactTriple (prefixes : List (String × String)) (j : Json) : Except String Triple := do
  match ← arr j with
  | [a, b, c] => return (← parseCompact prefixes a, ← parseCompact prefixes b, ← parseCompact prefixes c)
  | _ => throw "a claim has three terms"

def parseIncompat (prefixes : List (String × String)) (j : Json) :
    Except String (List (String × List Triple)) := do
  (← arr j).mapM fun x => do
    pure (← (← x.getObjVal? "entry").getStr?,
      ← (← arr (← x.getObjVal? "claims")).mapM (parseCompactTriple prefixes))

def parseCert (prefixes : List (String × String)) (j : Json) : Except String Cert := do
  let evalsJ ← j.getObjVal? "evaluations"
  let evals ← match evalsJ with
    | .obj kvs => kvs.toList.mapM fun (h, e) => do
      let bg ← match obj? e "background_incompatibilities" with
        | some b => parseIncompat prefixes b
        | none => pure []
      pure (h, { closure := ← (← arr (← e.getObjVal? "closure")).mapM (parseCompactTriple prefixes),
                 incompat := ← parseIncompat prefixes (← e.getObjVal? "incompatibilities"),
                 background := bg : CertEval })
    | _ => throw "evaluations must be an object"
  let apps ← (← arr (← j.getObjVal? "applications")).mapM fun a => do
    let binding ← match ← a.getObjVal? "binding" with
      | .obj kvs => kvs.toList.mapM fun (v, t) => do pure (v, ← parseCompact prefixes t)
      | _ => throw "a binding is an object"
    let conclusion ← match ← a.getObjVal? "conclusion" with
      | .null => pure none
      | c => some <$> parseCompactTriple prefixes c
    let checks ← (← arr (← a.getObjVal? "defeater_checks")).mapM fun c => do
      pure ((← getInt (← c.getObjVal? "defeater")).toNat, ← (← c.getObjVal? "fires").getBool?)
    pure { holder := ← (← a.getObjVal? "holder").getStr?, entry := ← (← a.getObjVal? "entry").getStr?,
           binding, layer := ← getInt (← a.getObjVal? "layer"),
           premises := ← (← arr (← a.getObjVal? "premises")).mapM (parseCompactTriple prefixes),
           conclusion, checks : CertApp }
  let rounds ← (← arr (← (← j.getObjVal? "entitlement").getObjVal? "rounds")).mapM fun r => do
    (← arr r).mapM fun m => do
      pure (← (← m.getObjVal? "holder").getStr?, ← parseCompactTriple prefixes (← m.getObjVal? "claim"))
  return { evals, apps, rounds }

/-! ### One evaluation (the record, or one party) -/

/-- A ground instance of an enabling rule, with the rule it comes from. -/
structure Inst where
  rule : Nat
  binding : Binding
  premises : List Triple
  conclusion : Triple
  ground : GroundRule

structure EvalResult where
  holder : String
  closure : List Triple
  commitments : List Triple
  /-- (rule index, premises, conclusion) of every checked application. -/
  derivations : List (List Triple × Triple)
  incompat : List (String × List Triple)
  background : List (String × List Triple)

def keysOf (l : List Triple) : List String := l.map tripleKey

def defeaterAtoms (C : List Triple) (b : Binding) (d : List Pat × Option Guard) :
    List (List String) :=
  (solutions C d.1 d.2 b).map fun σ => (d.1.filterMap (applyPat σ)).map tripleKey

/-- Every instance of every enabling rule over `C`; for a party (`anchor =
some base`), only instances with a premise outside `base`. -/
def instances (rules : List Rule) (C : List Triple) (anchor : Option (List Triple)) : List Inst :=
  let all := rules.zipIdx.flatMap fun (r, ri) =>
    match r.conclusion with
    | none => []
    | some cp =>
      (solutions C r.premises r.guard []).filterMap fun b => do
        let prem := r.premises.filterMap (applyPat b)
        let concl ← applyPat b cp
        if prem.length != r.premises.length then none
        else if (match anchor with
            | some base => !prem.any (fun p => !base.contains p)
            | none => false) then none
        else some { rule := ri, binding := b, premises := prem, conclusion := concl,
                    ground := { name := r.name, layer := r.layer, premises := keysOf prem,
                                conclusion := some (tripleKey concl),
                                defeaters := r.defeaters.flatMap (defeaterAtoms C b) } }
  all.foldl (fun acc i => if acc.any (fun j => j.rule == i.rule && j.premises == i.premises)
    then acc else acc ++ [i]) []

/-- The open (and, for the record, background) incompatibilities over `C`. -/
def incompatibilities (rules : List Rule) (C : List Triple) (own : List Triple) (record : Bool) :
    List (String × List Triple) × List (String × List Triple) := Id.run do
  let mut opened : List (String × List Triple) := []
  let mut bg : List (String × List Triple) := []
  for r in rules do
    if r.conclusion.isNone then
      for b in solutions C r.premises r.guard [] do
        let defeated := r.defeaters.any fun d => !(solutions C d.1 d.2 b).isEmpty
        if !defeated then
          let members := dedup (r.premises.filterMap (applyPat b))
          if members.any (fun m => own.contains m) then opened := opened ++ [(r.name, members)]
          else if record then bg := bg ++ [(r.name, members)]
  return (opened, bg)

/-- Two incompatibility lists name the same set of (entry, member set). -/
def sameIncompat (a b : List (String × List Triple)) : Bool :=
  let norm (l : List (String × List Triple)) : List (String × List String) :=
    l.map fun (e, ms) => (e, dedup (keysOf ms))
  let sub (x y : List (String × List String)) : Bool :=
    x.all fun (e, ks) => y.any fun (e', ks') => e == e' && ks.all ks'.contains && ks'.all ks.contains
  sub (norm a) (norm b) && sub (norm b) (norm a)

def checkApp (rules : List Rule) (insts : List Inst) (a : CertApp) :
    Except String (GroundApplication × Inst) := do
  let some ri := rules.findIdx? (·.name == a.entry) | throw s!"application of unknown entry {a.entry}"
  let r := rules[ri]!
  let some cp := r.conclusion | throw s!"entry {a.entry} is an exclusion; it is never applied"
  let vars := dedup (r.premises.flatMap patVars)
  unless a.binding.all (fun (v, _) => vars.contains v) && vars.all (fun v => (lookupVar a.binding v).isSome) do
    throw s!"{a.entry}: the binding does not bind exactly the premise variables"
  let prem := r.premises.filterMap (applyPat a.binding)
  unless prem == a.premises do throw s!"{a.entry}: the premises are not the patterns under the binding"
  unless applyPat a.binding cp == a.conclusion do
    throw s!"{a.entry}: the conclusion is not the pattern under the binding"
  unless guardHolds r.guard a.binding do throw s!"{a.entry}: the guard does not hold for this binding"
  unless a.checks.length == r.defeaters.length &&
      (a.checks.zipIdx.all fun ((i, fires), k) => i == k && !fires) do
    throw s!"{a.entry}: there must be one defeater check per declared defeater, each finding it absent"
  if a.layer < 0 then throw s!"{a.entry}: a negative layer"
  let some gi := insts.findIdx? (fun i => i.rule == ri && i.premises == prem)
    | throw s!"{a.entry}: not an instance over the claimed closure for holder '{a.holder}' (or not attributable to it)"
  let some inst := insts[gi]? | throw "internal: instance index out of range"
  return ({ entry := gi, layer := a.layer.toNat,
            defeaterChecks := List.replicate inst.ground.defeaters.length true }, inst)

def evaluate (inp : Input) (cert : Cert) (holder : String) (facts : List Triple)
    (anchor : Option (List Triple)) (own : List Triple) : Except String EvalResult := do
  let some ce := cert.evals.lookup holder | throw s!"no evaluation for holder '{holder}'"
  let C := dedup ce.closure
  let insts := instances inp.rules C anchor
  let apps := cert.apps.filter (·.holder == holder)
  let checked ← apps.mapM (checkApp inp.rules insts)
  let gcert : GroundClosureCert := { applications := checked.map (·.1), closure := keysOf C }
  let grules := insts.map (·.ground)
  unless checkGroundClosure grules (keysOf facts) gcert do
    throw s!"holder '{holder}': the ground closure check failed (a layer, an order, a premise, a defeater, saturation or the closure itself)"
  let derivations := checked.map fun (_, i) => (i.premises, i.conclusion)
  let commitments := dedup (own ++ derivations.map (·.2))
  let base := match anchor with
    | some b => b
    | none => facts
  let ownX := C.filter (fun t => !base.contains t)
  let (opened, bg) := incompatibilities inp.rules C ownX anchor.isNone
  unless sameIncompat opened ce.incompat do
    throw s!"holder '{holder}': the open incompatibilities differ from the checker's"
  unless sameIncompat bg ce.background do
    throw s!"holder '{holder}': the background incompatibilities differ from the checker's"
  return { holder, closure := C, commitments, derivations, incompat := opened, background := bg }

/-! ### Entitlement -/

inductive Res where
  | node (i : Nat)
  | const (b : Bool)

def nodeIndex (keys : List (String × String)) (h : String) (t : Triple) : Option Nat :=
  keys.findIdx? (· == (h, tripleKey t))

def checkScore (inp : Input) (cert : Cert) : Except String Json := do
  -- the record
  let recFacts := dedup (inp.facts.map (·.claim))
  let known := "" :: inp.holders.map (·.name)
  unless cert.apps.all (fun a => known.contains a.holder) && cert.evals.all (fun e => known.contains e.1) do
    throw "the certificate names a holder that is neither the record nor a party of the input"
  let recE ← evaluate inp cert "" recFacts none []
  -- the parties
  let recClosure := recE.closure
  let parties ← inp.holders.mapM fun h => do
    let own := dedup (h.undertakings.map (·.claim))
    evaluate inp cert h.name (dedup (recClosure ++ own)) (some recClosure) own
  let evs := recE :: parties
  -- nodes
  let keys : List (String × String) :=
    evs.flatMap fun e => (e.commitments.map tripleKey).map (e.holder, ·)
  let partyNames := inp.holders.map (·.name)
  let commitsOf (h : String) : List Triple := match evs.find? (·.holder == h) with
    | some e => e.commitments
    | none => []
  let bgMembers := recE.background.flatMap (·.2)
  let factsOK (t : Triple) : Bool :=
    match inp.facts.find? (·.claim == t) with
    | some f =>
      let trusted := f.sources.contains none
      let ok := trusted || f.sources.any (fun s => match s with
        | some a => !inp.challenged.contains a
        | none => false)
      if bgMembers.contains t && !trusted then false else ok
    | none => false
  let resolve (h : Option String) (t : Triple) : Res :=
    match h with
    | some name =>
      if name != "" && partyNames.contains name && (commitsOf name).contains t then
        match nodeIndex keys name t with
        | some i => .node i
        | none => .const false
      else if recE.commitments.contains t then
        match nodeIndex keys "" t with
        | some i => .node i
        | none => .const false
      else .const (factsOK t)
    | none =>
      if recE.commitments.contains t then
        match nodeIndex keys "" t with
        | some i => .node i
        | none => .const false
      else .const (factsOK t)
  let support (h : String) (prem : List Triple) : Option (List Nat) :=
    prem.foldl (fun acc p => do
      let s ← acc
      match resolve (some h) p with
      | .node i => some (s ++ [i])
      | .const true => some s
      | .const false => none) (some [])
  let nodes : List EntitlementNode := evs.flatMap fun e =>
    let undertakings := match inp.holders.find? (·.name == e.holder) with
      | some h => h.undertakings
      | none => []
    let blockedSet := e.incompat.flatMap (·.2)
    e.commitments.map fun t =>
      let (dflt, dsup) : Bool × List (List Nat) :=
        if e.holder == "" then (false, []) else
        match undertakings.find? (·.claim == t) with
        | none => (false, [])
        | some u =>
          if inp.challenged.contains u.act then (false, [])
          else if u.kind == "defer" then
            if u.to == some e.holder then (false, [])
            else match resolve u.to t with
              | .node i => (false, [[i]])
              | .const b => (b, [])
          else (true, [])
      let dsups := (e.derivations.filter (·.2 == t)).filterMap fun (prem, _) => support e.holder prem
      { holder := e.holder, claim := tripleKey t, defaultOK := dflt, blocked := blockedSet.contains t,
        supports := dsup ++ dsups }
  let rounds ← cert.rounds.mapM fun r => r.mapM fun (h, t) =>
    match nodeIndex keys h t with
    | some i => pure i
    | none => throw s!"an entitlement round grants '{h}' a claim that is not one of its commitments"
  unless checkEntitlement nodes rounds do
    throw "the entitlement rounds are not the synchronous steps from the empty set to the least fixpoint"
  let last := rounds.getLast?.getD []
  -- the projection
  let compactTerm : Term → Except String Json
    | .int i => pure (Json.num (JsonNumber.fromInt i))
    | .str s => pure (Json.mkObj [("lit", Json.str s)])
    | .iri s => match inp.prefixes.find? (fun (_, ns) => s.startsWith ns && s.length > ns.length) with
      | some (p, ns) => pure (Json.str (p ++ ":" ++ toString (s.drop ns.length)))
      | none => throw s!"no prefix for {s}"
  let claimJ (t : Triple) : Except String Json := do
    pure (Json.arr #[← compactTerm t.1, ← compactTerm t.2.1, ← compactTerm t.2.2])
  let sorted (items : List Json) : Except String Json := do
    let keyed ← items.mapM fun j => do pure (← NMMS.Wire.canonical j, j)
    let uniq := keyed.foldl (fun acc kv => if acc.any (·.1 == kv.1) then acc else acc ++ [kv]) []
    let ordered := (uniq.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (·.2)
    pure (Json.arr ordered.toArray)
  let incompatJ (l : List (String × List Triple)) : Except String Json := do
    sorted (← l.mapM fun (e, ms) => do
      pure (Json.mkObj [("entry", Json.str e), ("claims", ← sorted (← ms.mapM claimJ))]))
  let position (e : EvalResult) : Except String (List (String × Json)) := do
    let ents := e.commitments.filter fun t => match nodeIndex keys e.holder t with
      | some i => last.contains i
      | none => false
    pure [("commitments", ← sorted (← e.commitments.mapM claimJ)),
          ("entitlements", ← sorted (← ents.mapM claimJ)),
          ("incompatibilities", ← incompatJ e.incompat)]
  let recordJ := Json.mkObj ((← position recE) ++
    [("background_incompatibilities", ← incompatJ recE.background)])
  let partiesJ ← parties.mapM fun e => do pure (e.holder, Json.mkObj (← position e))
  return Json.mkObj [("record", recordJ), ("parties", Json.mkObj partiesJ)]

/-- Answer an `"op": "score"` request (see the header and `Main.lean`). -/
def handle (j : Json) (id : Json) : Except String Json := do
  let given := (obj? j "request_hash").getD Json.null
  let inputJ ← j.getObjVal? "input"
  let expected ← NMMS.Wire.digest (Json.mkObj [("op", Json.str "score"), ("input", inputJ)])
  let reply (fields : List (String × Json)) : Json :=
    Json.mkObj ([("id", id), ("request_hash", given)] ++ fields)
  if given != Json.str expected then
    return reply [("accepted", Json.bool false),
      ("reason", Json.str "request_hash does not match the canonical hash of op and input")]
  let inp ← parseInput inputJ
  let cert ← parseCert inp.prefixes (← j.getObjVal? "certificate")
  match checkScore inp cert with
  | .ok score => return reply [("accepted", Json.bool true), ("score", score)]
  | .error reason => return reply [("accepted", Json.bool false), ("reason", Json.str reason)]

end NMMS.Score
