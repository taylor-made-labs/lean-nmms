/-
  LeanNmms.Certificate

  A prototype checker for "derivable" certificates. A certificate is a proof
  tree that names, at each node, the side and principal sentence of the rule
  applied, with one certificate per premise; leaves are axiom checks
  (pyNMMS's `_is_axiom`: a shared complex sentence, a shared atom, or a base
  match for an atomic sequent). The checker recomputes every premise sequent
  itself, so a certificate only carries choices, never sequents, and cannot
  smuggle in a wrong premise.

  `check_sound` proves that a certificate that checks yields a derivation, for
  every base. Checking costs one pass over the tree, with list-membership work
  at each node: linear in the tree size times the side length. Unlike `prove`,
  it never searches.

  `findCert` builds a certificate by the same search as `proveN`; the harness
  instead builds certificates from pyNMMS's own proof traces and has this
  checker verify them (see README, "Certificates").

  Single-premise rules use `c1` only; `c2` and `c3` are ignored (by convention
  `.ax`).
-/
import LeanNmms.Decide

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- A proof-tree certificate. `left = true` for a left rule. -/
inductive Cert (α : Type) where
  | ax : Cert α
  | node (left : Bool) (φ : Formula α) (c1 c2 c3 : Cert α) : Cert α
  deriving Repr, Inhabited

/-- Number of nodes (the checking cost, up to side length). -/
def Cert.size : Cert α → Nat
  | .ax => 1
  | .node _ _ c1 c2 c3 => c1.size + c2.size + c3.size + 1

/-- The certificate checker. -/
def check (R : BaseRel α) : Cert α → List (Formula α) → List (Formula α) → Bool
  | .ax, Γ, Δ => axiomCheck R Γ Δ
  | .node true φ c1 c2 c3, Γ, Δ => Γ.contains φ &&
      match φ with
      | atom _ => false
      | neg A => check R c1 (rest Γ φ) (A :: Δ)
      | impl A B => check R c1 (rest Γ φ) (A :: Δ) && check R c2 (B :: rest Γ φ) Δ &&
          check R c3 (B :: rest Γ φ) (A :: Δ)
      | conj A B => check R c1 (A :: B :: rest Γ φ) Δ
      | disj A B => check R c1 (A :: rest Γ φ) Δ && check R c2 (B :: rest Γ φ) Δ &&
          check R c3 (A :: B :: rest Γ φ) Δ
  | .node false φ c1 c2 c3, Γ, Δ => Δ.contains φ &&
      match φ with
      | atom _ => false
      | neg A => check R c1 (A :: Γ) (rest Δ φ)
      | impl A B => check R c1 (A :: Γ) (B :: rest Δ φ)
      | conj A B => check R c1 Γ (A :: rest Δ φ) && check R c2 Γ (B :: rest Δ φ) &&
          check R c3 Γ (A :: B :: rest Δ φ)
      | disj A B => check R c1 Γ (A :: B :: rest Δ φ)

/-- **Certificate soundness**: a certificate that checks is a derivation. -/
theorem check_sound (R : BaseRel α) :
    ∀ (c : Cert α) Γ Δ, check R c Γ Δ = true → Derivable R Γ Δ := by
  intro c
  induction c with
  | ax => intro Γ Δ h; exact axiomCheck_sound h
  | node left φ c1 c2 c3 ih1 ih2 ih3 =>
    intro Γ Δ h
    cases left with
    | true =>
      simp only [check, Bool.and_eq_true, List.contains_iff_mem] at h
      obtain ⟨hm, h⟩ := h
      cases φ with
      | atom a => simp at h
      | neg A => exact Derivable.negL hm (ih1 _ _ h)
      | impl A B =>
        simp only [Bool.and_eq_true] at h
        exact Derivable.implL hm (ih1 _ _ h.1.1) (ih2 _ _ h.1.2) (ih3 _ _ h.2)
      | conj A B => exact Derivable.conjL hm (ih1 _ _ h)
      | disj A B =>
        simp only [Bool.and_eq_true] at h
        exact Derivable.disjL hm (ih1 _ _ h.1.1) (ih2 _ _ h.1.2) (ih3 _ _ h.2)
    | false =>
      simp only [check, Bool.and_eq_true, List.contains_iff_mem] at h
      obtain ⟨hm, h⟩ := h
      cases φ with
      | atom a => simp at h
      | neg A => exact Derivable.negR hm (ih1 _ _ h)
      | impl A B => exact Derivable.implR hm (ih1 _ _ h)
      | conj A B =>
        simp only [Bool.and_eq_true] at h
        exact Derivable.conjR hm (ih1 _ _ h.1.1) (ih2 _ _ h.1.2) (ih3 _ _ h.2)
      | disj A B => exact Derivable.disjR hm (ih1 _ _ h)

/-- Build a certificate by root-first search (same strategy as `proveN`). -/
def findCert (R : BaseRel α) : Nat → List (Formula α) → List (Formula α) → Option (Cert α)
  | 0, _, _ => none
  | n + 1, Γ, Δ =>
    if axiomCheck R Γ Δ then some .ax else
    let tryL : Formula α → Option (Cert α) := fun φ =>
      match φ with
      | atom _ => none
      | neg A => (findCert R n (rest Γ φ) (A :: Δ)).map (fun c => .node true φ c .ax .ax)
      | impl A B => do
          let c1 ← findCert R n (rest Γ φ) (A :: Δ)
          let c2 ← findCert R n (B :: rest Γ φ) Δ
          let c3 ← findCert R n (B :: rest Γ φ) (A :: Δ)
          pure (.node true φ c1 c2 c3)
      | conj A B => (findCert R n (A :: B :: rest Γ φ) Δ).map (fun c => .node true φ c .ax .ax)
      | disj A B => do
          let c1 ← findCert R n (A :: rest Γ φ) Δ
          let c2 ← findCert R n (B :: rest Γ φ) Δ
          let c3 ← findCert R n (A :: B :: rest Γ φ) Δ
          pure (.node true φ c1 c2 c3)
    let tryR : Formula α → Option (Cert α) := fun φ =>
      match φ with
      | atom _ => none
      | neg A => (findCert R n (A :: Γ) (rest Δ φ)).map (fun c => .node false φ c .ax .ax)
      | impl A B =>
          (findCert R n (A :: Γ) (B :: rest Δ φ)).map (fun c => .node false φ c .ax .ax)
      | conj A B => do
          let c1 ← findCert R n Γ (A :: rest Δ φ)
          let c2 ← findCert R n Γ (B :: rest Δ φ)
          let c3 ← findCert R n Γ (A :: B :: rest Δ φ)
          pure (.node false φ c1 c2 c3)
      | disj A B =>
          (findCert R n Γ (A :: B :: rest Δ φ)).map (fun c => .node false φ c .ax .ax)
    match Γ.findSome? tryL with
    | some c => some c
    | none => Δ.findSome? tryR

end NMMS
