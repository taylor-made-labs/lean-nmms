/-
  LeanNmms.Certificate

  A checker for "derivable" certificates. A certificate is a proof tree that
  names, at each node, the side and principal sentence of the rule applied,
  whether the rule's context keeps the principal sentence, and one
  certificate per premise; leaves are axioms, i.e. atomic sequents in the
  base (nothing else: a leaf whose sides share a sentence is rejected unless
  it is an atomic base sequent). The checker recomputes every premise sequent
  itself, so a certificate only carries choices, never sequents, and cannot
  smuggle in a wrong premise.

  The book's rules are stated with `Γ, φ` read as `Γ ∪ {φ}`, so a conclusion
  `Γ ⇒ Δ` with `φ ∈ Γ` is an instance of φ's rule in two ways: with context
  `Γ ∖ {φ}` (`keep = false`, the usual reading and the one pyNMMS and the
  searches use) or with context `Γ` itself (`keep = true`). Up to set
  equality there are no other contexts, so the checker accepts exactly the
  book's derivation trees.

  * `check_sound`: a certificate that checks is a derivation, for every base.
  * `check_complete`: every derivable sequent has a certificate that checks
    (with `keep = false` throughout), over every set-invariant base.

  Checking costs one pass over the tree, with list-membership work at each
  node: linear in the tree size times the side length. Unlike the searches,
  it never searches.

  Single-premise rules use `c1` only; `c2` and `c3` are ignored (by convention
  `.ax`).
-/
import LeanNmms.Decide

namespace NMMS

open Formula

variable {α : Type} [DecidableEq α]

/-- A proof-tree certificate. `left = true` for a left rule; `keep = true`
when the rule's context keeps the principal sentence. -/
inductive Cert (α : Type) where
  | ax : Cert α
  | node (left : Bool) (φ : Formula α) (keep : Bool) (c1 c2 c3 : Cert α) : Cert α
  deriving Repr, Inhabited

/-- Number of nodes (the checking cost, up to side length). -/
def Cert.size : Cert α → Nat
  | .ax => 1
  | .node _ _ _ c1 c2 c3 => c1.size + c2.size + c3.size + 1

/-- The context of a rule on `φ`: the side without `φ`, or the whole side. -/
def ctx (keep : Bool) (l : List (Formula α)) (φ : Formula α) : List (Formula α) :=
  if keep then l else rest l φ

theorem setEq_ctx {keep : Bool} {l : List (Formula α)} {φ : Formula α} (h : φ ∈ l) :
    SetEq l (φ :: ctx keep l φ) := by
  cases keep
  · exact setEq_cons_rest h
  · exact setEq_cons_self h

/-- The certificate checker. -/
def check (R : BaseRel α) : Cert α → List (Formula α) → List (Formula α) → Bool
  | .ax, Γ, Δ => axiomCheck R Γ Δ
  | .node true φ keep c1 c2 c3, Γ, Δ => Γ.contains φ &&
      match φ with
      | atom _ => false
      | neg A => check R c1 (ctx keep Γ φ) (A :: Δ)
      | impl A B => check R c1 (ctx keep Γ φ) (A :: Δ) && check R c2 (B :: ctx keep Γ φ) Δ &&
          check R c3 (B :: ctx keep Γ φ) (A :: Δ)
      | conj A B => check R c1 (A :: B :: ctx keep Γ φ) Δ
      | disj A B => check R c1 (A :: ctx keep Γ φ) Δ && check R c2 (B :: ctx keep Γ φ) Δ &&
          check R c3 (A :: B :: ctx keep Γ φ) Δ
  | .node false φ keep c1 c2 c3, Γ, Δ => Δ.contains φ &&
      match φ with
      | atom _ => false
      | neg A => check R c1 (A :: Γ) (ctx keep Δ φ)
      | impl A B => check R c1 (A :: Γ) (B :: ctx keep Δ φ)
      | conj A B => check R c1 Γ (A :: ctx keep Δ φ) && check R c2 Γ (B :: ctx keep Δ φ) &&
          check R c3 Γ (A :: B :: ctx keep Δ φ)
      | disj A B => check R c1 Γ (A :: B :: ctx keep Δ φ)

/-- **Certificate soundness**: a certificate that checks is a derivation. -/
theorem check_sound (R : BaseRel α) :
    ∀ (c : Cert α) Γ Δ, check R c Γ Δ = true → Derivable R Γ Δ := by
  intro c
  induction c with
  | ax => intro Γ Δ h; exact axiomCheck_sound h
  | node left φ keep c1 c2 c3 ih1 ih2 ih3 =>
    intro Γ Δ h
    cases left with
    | true =>
      simp only [check, Bool.and_eq_true, List.contains_iff_mem] at h
      obtain ⟨hm, h⟩ := h
      have e := setEq_ctx (keep := keep) hm
      cases φ with
      | atom a => simp at h
      | neg A => exact Derivable.negL e (ih1 _ _ h)
      | impl A B =>
        simp only [Bool.and_eq_true] at h
        exact Derivable.implL e (ih1 _ _ h.1.1) (ih2 _ _ h.1.2) (ih3 _ _ h.2)
      | conj A B => exact Derivable.conjL e (ih1 _ _ h)
      | disj A B =>
        simp only [Bool.and_eq_true] at h
        exact Derivable.disjL e (ih1 _ _ h.1.1) (ih2 _ _ h.1.2) (ih3 _ _ h.2)
    | false =>
      simp only [check, Bool.and_eq_true, List.contains_iff_mem] at h
      obtain ⟨hm, h⟩ := h
      have e := setEq_ctx (keep := keep) hm
      cases φ with
      | atom a => simp at h
      | neg A => exact Derivable.negR e (ih1 _ _ h)
      | impl A B => exact Derivable.implR e (ih1 _ _ h)
      | conj A B =>
        simp only [Bool.and_eq_true] at h
        exact Derivable.conjR e (ih1 _ _ h.1.1) (ih2 _ _ h.1.2) (ih3 _ _ h.2)
      | disj A B => exact Derivable.disjR e (ih1 _ _ h)

/-- **Certificate completeness**: every derivable sequent has a certificate
that checks, over every set-invariant base. -/
theorem check_complete {R : BaseRel α} (hR : R.SetInvariant) {Γ Δ : List (Formula α)}
    (h : Derivable R Γ Δ) : ∃ c, check R c Γ Δ = true := by
  refine decompose_of_preserved (Derivable R) (fun Γ Δ => ∃ c, check R c Γ Δ = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (measure Γ Δ + 1) Γ Δ (by omega) h
  · intro Γ Δ hg hd hD
    exact ⟨.ax, axiomCheck_iff.mpr ⟨hg, hd, derivable_atomic hg hd hD⟩⟩
  · intro Γ Δ A hm hD; exact negL_inv hR hm hD
  · intro Γ Δ A B hm hD; exact implL_inv hR hm hD
  · intro Γ Δ A B hm hD; exact conjL_inv hR hm hD
  · intro Γ Δ A B hm hD; exact disjL_inv hR hm hD
  · intro Γ Δ A hm hD; exact negR_inv hR hm hD
  · intro Γ Δ A B hm hD; exact implR_inv hR hm hD
  · intro Γ Δ A B hm hD; exact conjR_inv hR hm hD
  · intro Γ Δ A B hm hD; exact disjR_inv hR hm hD
  · intro Γ Δ A hm ⟨c, hc⟩
    exact ⟨.node true (neg A) false c .ax .ax, by simp [check, hm, ctx, hc]⟩
  · intro Γ Δ A B hm ⟨c1, h1⟩ ⟨c2, h2⟩ ⟨c3, h3⟩
    exact ⟨.node true (impl A B) false c1 c2 c3, by simp [check, hm, ctx, h1, h2, h3]⟩
  · intro Γ Δ A B hm ⟨c, hc⟩
    exact ⟨.node true (conj A B) false c .ax .ax, by simp [check, hm, ctx, hc]⟩
  · intro Γ Δ A B hm ⟨c1, h1⟩ ⟨c2, h2⟩ ⟨c3, h3⟩
    exact ⟨.node true (disj A B) false c1 c2 c3, by simp [check, hm, ctx, h1, h2, h3]⟩
  · intro Γ Δ A hm ⟨c, hc⟩
    exact ⟨.node false (neg A) false c .ax .ax, by simp [check, hm, ctx, hc]⟩
  · intro Γ Δ A B hm ⟨c, hc⟩
    exact ⟨.node false (impl A B) false c .ax .ax, by simp [check, hm, ctx, hc]⟩
  · intro Γ Δ A B hm ⟨c1, h1⟩ ⟨c2, h2⟩ ⟨c3, h3⟩
    exact ⟨.node false (conj A B) false c1 c2 c3, by simp [check, hm, ctx, h1, h2, h3]⟩
  · intro Γ Δ A B hm ⟨c, hc⟩
    exact ⟨.node false (disj A B) false c .ax .ax, by simp [check, hm, ctx, hc]⟩

/-- `check` accepts a certificate exactly for the derivable sequents. -/
theorem certifiable_iff {R : BaseRel α} (hR : R.SetInvariant) (Γ Δ : List (Formula α)) :
    (∃ c, check R c Γ Δ = true) ↔ Derivable R Γ Δ :=
  ⟨fun ⟨c, hc⟩ => check_sound R c Γ Δ hc, check_complete hR⟩

/-- Build a certificate by the non-backtracking search (same strategy as
`fastN`); `check_complete` is the matching existence theorem. -/
def findCert (R : BaseRel α) : Nat → List (Formula α) → List (Formula α) → Option (Cert α)
  | 0, _, _ => none
  | n + 1, Γ, Δ =>
    match pickComplex Γ Δ with
    | none => if axiomCheck R Γ Δ then some .ax else none
    | some (b, φ) => do
      let cs ← (premises b φ Γ Δ).mapM (fun p => findCert R n p.1 p.2)
      pure (.node b φ false (cs.getD 0 .ax) (cs.getD 1 .ax) (cs.getD 2 .ax))

end NMMS
