/-
  LeanNmms.Entitlement

  The entitlement least fixpoint over ground nodes, and a checker for its
  synchronous rounds (fix 3 of the 21 Oct 2026 adversarial review).

  A node is one holder's commitment to one claim (holder and claim are part
  of its identity; the empty holder is the shared record). It is entitled
  when it is not `blocked` (in one of its holder's open incompatibilities)
  and either `defaultOK` (an undertaking with standing: not challenged, not a
  deferral) or one of its `supports` lists only entitled nodes. A support
  is a derivation's premises (or a deferral's target) that need entitlement;
  an empty support is a source that needs none; a node with no supports and
  no default is never entitled. `Entitled` is the least such set (an
  inductive predicate), so a cycle of supports alone grants nothing.

  `checkEntitlement nodes rounds` requires the first round to be empty, each
  next round to equal the synchronous step applied to the previous one (as
  sets), and the last round to be a fixpoint of the step.
  `checkEntitlement_sound`: the last round is then exactly `Entitled`
  (`EntitlementExact`). The external Python library whose certificates
  `LeanNmms.Score` checks computes the same least
  fixpoint by chaotic iteration; its step is monotone, so the two agree.
-/

namespace NMMS

structure EntitlementNode where
  holder : String
  claim : String
  defaultOK : Bool
  blocked : Bool
  supports : List (List Nat)
  deriving Repr, DecidableEq

/-- The least set of entitled nodes. -/
inductive Entitled (nodes : List EntitlementNode) : Nat → Prop where
  | byDefault {i : Nat} (n : EntitlementNode) : nodes[i]? = some n → n.blocked = false →
      n.defaultOK = true → Entitled nodes i
  | bySupport {i : Nat} (n : EntitlementNode) (s : List Nat) : nodes[i]? = some n →
      n.blocked = false → s ∈ n.supports → (∀ j ∈ s, Entitled nodes j) → Entitled nodes i

/-- The last supplied round is exactly the least fixpoint. -/
def EntitlementExact (nodes : List EntitlementNode) (rounds : List (List Nat)) : Prop :=
  ∃ last, rounds.getLast? = some last ∧ ∀ i, i ∈ last ↔ Entitled nodes i

/-- Is node `n` entitled given the set `E`? -/
def nodeOK (E : List Nat) (n : EntitlementNode) : Bool :=
  !n.blocked && (n.defaultOK || n.supports.any (fun s => s.all (fun j => E.contains j)))

/-- The synchronous step. -/
def stepE (nodes : List EntitlementNode) (E : List Nat) : List Nat :=
  (List.range nodes.length).filter fun i =>
    match nodes[i]? with
    | some n => nodeOK E n
    | none => false

def sameSet (a b : List Nat) : Bool := a.all (fun x => b.contains x) && b.all (fun x => a.contains x)

/-- Each round is the step of the one before; the last is fixed. -/
def checkRounds (nodes : List EntitlementNode) : List Nat → List (List Nat) → Bool
  | prev, [] => sameSet (stepE nodes prev) prev
  | prev, r :: rest => sameSet r (stepE nodes prev) && checkRounds nodes r rest

/-- The entitlement rounds checker (see the module header). -/
def checkEntitlement (nodes : List EntitlementNode) (rounds : List (List Nat)) : Bool :=
  match rounds with
  | [] => false
  | r0 :: rest => r0.isEmpty && checkRounds nodes r0 rest

theorem mem_stepE {nodes : List EntitlementNode} {E : List Nat} {i : Nat} :
    i ∈ stepE nodes E ↔ ∃ n, nodes[i]? = some n ∧ nodeOK E n = true := by
  unfold stepE
  simp only [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hi, h⟩
    split at h
    · rename_i n hn; exact ⟨n, hn, h⟩
    · simp at h
  · rintro ⟨n, hn, h⟩
    refine ⟨(List.getElem?_eq_some_iff.mp hn).1, ?_⟩
    rw [hn]; exact h

theorem sameSet_iff {a b : List Nat} : sameSet a b = true ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact ⟨fun ⟨h1, h2⟩ x => ⟨h1 x, h2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

/-- The step keeps inside `Entitled`. -/
theorem stepE_sound {nodes : List EntitlementNode} {E : List Nat}
    (hE : ∀ j ∈ E, Entitled nodes j) : ∀ i ∈ stepE nodes E, Entitled nodes i := by
  intro i hi
  obtain ⟨n, hn, hok⟩ := mem_stepE.mp hi
  simp only [nodeOK, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, List.any_eq_true,
    List.all_eq_true, List.contains_iff_mem] at hok
  obtain ⟨hb, hd⟩ := hok
  rcases hd with hd | ⟨s, hs, hall⟩
  · exact Entitled.byDefault n hn hb hd
  · exact Entitled.bySupport n s hn hb hs (fun j hj => hE j (hall j hj))

/-- A fixpoint of the step contains `Entitled`. -/
theorem fixed_complete {nodes : List EntitlementNode} {E : List Nat}
    (hfix : ∀ x, x ∈ stepE nodes E ↔ x ∈ E) : ∀ i, Entitled nodes i → i ∈ E := by
  intro i h
  induction h with
  | @byDefault i n hn hb hd =>
    apply (hfix i).mp
    apply mem_stepE.mpr
    refine ⟨n, hn, ?_⟩
    simp [nodeOK, hb, hd]
  | @bySupport i n s hn hb hs _ ih =>
    apply (hfix i).mp
    apply mem_stepE.mpr
    refine ⟨n, hn, ?_⟩
    simp only [nodeOK, hb, Bool.not_false, Bool.true_and, Bool.or_eq_true, List.any_eq_true,
      List.all_eq_true, List.contains_iff_mem]
    exact Or.inr ⟨s, hs, ih⟩

theorem checkRounds_sound {nodes : List EntitlementNode} :
    ∀ (rest : List (List Nat)) (prev : List Nat), (∀ j ∈ prev, Entitled nodes j) →
      checkRounds nodes prev rest = true →
      ∀ i, i ∈ (prev :: rest).getLast (List.cons_ne_nil _ _) ↔ Entitled nodes i
  | [], prev, hprev, h => by
    simp only [checkRounds] at h
    have hfix := sameSet_iff.mp h
    intro i
    exact ⟨fun hi => hprev i hi, fun hi => fixed_complete hfix i hi⟩
  | r :: rest, prev, hprev, h => by
    simp only [checkRounds, Bool.and_eq_true] at h
    obtain ⟨hr, hrest⟩ := h
    have hrE : ∀ j ∈ r, Entitled nodes j := by
      intro j hj
      exact stepE_sound hprev j ((sameSet_iff.mp hr j).mp hj)
    have := checkRounds_sound rest r hrE hrest
    simpa [List.getLast_cons] using this

/-- **Entitlement soundness**: accepted rounds end exactly at the least
fixpoint. -/
theorem checkEntitlement_sound {nodes : List EntitlementNode} {rounds : List (List Nat)}
    (h : checkEntitlement nodes rounds = true) : EntitlementExact nodes rounds := by
  unfold checkEntitlement at h
  split at h
  · simp at h
  · rename_i r0 rest
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨h0, hrest⟩ := h
    subst h0
    refine ⟨(([] : List Nat) :: rest).getLast (List.cons_ne_nil _ _), ?_, ?_⟩
    · exact List.getLast?_eq_some_getLast _
    · exact checkRounds_sound rest [] (fun j hj => by simp at hj) hrest

end NMMS
