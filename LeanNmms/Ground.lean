/-
  LeanNmms.Ground

  Stratified defeasible closure over ground atoms, and a checker for a
  claimed closure with its rule applications. The score checker
  (`LeanNmms.Score`) grounds the rules of an external Python library and uses
  this core for the record and for every party.

  **Semantics.** Atoms are uninterpreted strings. A ground rule has a layer,
  premises, a conclusion (`none` for an exclusion, which never adds atoms)
  and defeaters, each a conjunction of atoms. Layers are processed in
  increasing order. `Stage l` is the least set that contains everything
  below layer `l` (`Below l`: the facts for layer 0, else `Stage (l - 1)`) and
  is closed under the rules of layer `l` whose premises are in it and none
  of whose defeaters is wholly contained in `Below l`. A rule of layer `l`
  sees only the completed lower layers for its defeaters, and atoms up to
  its own layer for its premises; a later layer never re-opens an earlier
  one. `GroundClosure` is the last stage. This is that library's
  evaluation: layer by layer, each to a fixpoint, defeaters checked against
  what lower layers concluded (its base check refuses a defeater that its own
  or a later layer could switch on).

  **Checker.** A certificate lists applications (rule index, layer, one
  Boolean per defeater) in order, and the claimed closure. `checkGroundClosure`
  requires: the rules are stratified (an atom of a defeater is concluded only
  by rules of a lower layer); each application names an enabling rule, carries
  its declared layer, and comes after no application of a higher layer; its premises are facts or
  conclusions of earlier applications; it has exactly one check per defeater,
  each `true`, and the checker recomputes that the defeater does not fire on
  the facts plus the conclusions of lower-layer applications; no rule is
  applied twice; every rule that is applicable (premises available up to its
  layer, no defeater firing below it) is applied (saturation); and the
  closure is exactly the facts plus the conclusions.

  **Theorems.** `checkGroundClosure_exact`: an accepted certificate's closure
  is exactly `GroundClosure`, and a rule is applied exactly when it is
  `Applicable`. `checkGroundClosure_sound` is the first half's one direction.
-/

namespace NMMS

/-- A ground rule; `conclusion = none` is an exclusion. -/
structure GroundRule where
  name : String
  layer : Nat
  premises : List String
  conclusion : Option String
  defeaters : List (List String)
  deriving Repr, DecidableEq

/-- One application: the rule's index, its layer, one check per defeater. -/
structure GroundApplication where
  entry : Nat
  layer : Nat
  defeaterChecks : List Bool
  deriving Repr, DecidableEq

structure GroundClosureCert where
  applications : List GroundApplication
  closure : List String
  deriving Repr

/-! ### Semantics -/

/-- A defeater fires on a set when all of its atoms are in it. -/
def Fires (below : String → Prop) (d : List String) : Prop := ∀ x ∈ d, below x

/-- Closure of `below` under the rules of layer `l`. -/
inductive LayerReach (rules : List GroundRule) (below : String → Prop) (l : Nat) :
    String → Prop where
  | base {a : String} : below a → LayerReach rules below l a
  | app {r : GroundRule} {a : String} : r ∈ rules → r.layer = l → r.conclusion = some a →
      (∀ p ∈ r.premises, LayerReach rules below l p) →
      (∀ d ∈ r.defeaters, ¬ Fires below d) → LayerReach rules below l a

/-- Everything reached up to and including layer `l`. -/
def Stage (rules : List GroundRule) (facts : List String) : Nat → String → Prop
  | 0 => LayerReach rules (fun a => a ∈ facts) 0
  | n + 1 => LayerReach rules (Stage rules facts n) (n + 1)

/-- Everything reached below layer `l`. -/
def Below (rules : List GroundRule) (facts : List String) : Nat → String → Prop
  | 0 => fun a => a ∈ facts
  | n + 1 => Stage rules facts n

def maxLayer (rules : List GroundRule) : Nat := rules.foldr (fun r m => max r.layer m) 0

/-- The stratified defeasible closure of `facts` under `rules`. -/
def GroundClosure (rules : List GroundRule) (facts : List String) (a : String) : Prop :=
  Stage rules facts (maxLayer rules) a

/-- A rule that the semantics applies: enabling, premises reached up to its
layer, no defeater firing below it. -/
def Applicable (rules : List GroundRule) (facts : List String) (r : GroundRule) : Prop :=
  (∃ c, r.conclusion = some c) ∧ (∀ p ∈ r.premises, Stage rules facts r.layer p) ∧
    ∀ d ∈ r.defeaters, ¬ Fires (Below rules facts r.layer) d

/-! ### Checker -/

def conclOf (rules : List GroundRule) (ap : GroundApplication) : Option String :=
  match rules[ap.entry]? with
  | some r => r.conclusion
  | none => none

/-- In the facts, or concluded by an application of layer at most `l`. -/
def inUpTo (rules : List GroundRule) (facts : List String) (apps : List GroundApplication)
    (l : Nat) (a : String) : Bool :=
  facts.contains a || apps.any (fun ap => decide (ap.layer ≤ l) && conclOf rules ap == some a)

/-- In the facts, or concluded by an application of layer below `l`. -/
def inBelow (rules : List GroundRule) (facts : List String) (apps : List GroundApplication)
    (l : Nat) (a : String) : Bool :=
  facts.contains a || apps.any (fun ap => decide (ap.layer < l) && conclOf rules ap == some a)

def stratified (rules : List GroundRule) : Bool :=
  rules.all fun r => r.defeaters.all fun d => d.all fun x =>
    rules.all fun r' => r'.conclusion != some x || decide (r'.layer < r.layer)

/-- The checks on the application at position `k`. -/
def appOK (rules : List GroundRule) (facts : List String) (apps : List GroundApplication)
    (k : Nat) (ap : GroundApplication) : Bool :=
  match rules[ap.entry]? with
  | none => false
  | some r =>
    r.conclusion.isSome && ap.layer == r.layer &&
    ap.defeaterChecks.length == r.defeaters.length && ap.defeaterChecks.all id &&
    r.defeaters.all (fun d => !d.all (inBelow rules facts apps ap.layer)) &&
    r.premises.all (fun p => facts.contains p ||
      (apps.take k).any (fun aj => conclOf rules aj == some p)) &&
    (apps.take k).all (fun aj => decide (aj.layer ≤ ap.layer))

def appsOK (rules : List GroundRule) (facts : List String) (apps : List GroundApplication) :
    Bool :=
  (List.range apps.length).all fun k =>
    match apps[k]? with
    | some ap => appOK rules facts apps k ap
    | none => false

/-- The checker's reading of `Applicable`. -/
def applicableB (rules : List GroundRule) (facts : List String) (apps : List GroundApplication)
    (r : GroundRule) : Bool :=
  r.conclusion.isSome && r.premises.all (inUpTo rules facts apps r.layer) &&
    r.defeaters.all (fun d => !d.all (inBelow rules facts apps r.layer))

def saturated (rules : List GroundRule) (facts : List String) (apps : List GroundApplication) :
    Bool :=
  (List.range rules.length).all fun i =>
    match rules[i]? with
    | some r => !applicableB rules facts apps r || apps.any (fun ap => ap.entry == i)
    | none => true

def closureOK (rules : List GroundRule) (facts : List String) (apps : List GroundApplication)
    (closure : List String) : Bool :=
  closure.all (fun a => facts.contains a || apps.any (fun ap => conclOf rules ap == some a)) &&
  facts.all (fun a => closure.contains a) &&
  apps.all (fun ap => match conclOf rules ap with
    | some c => closure.contains c
    | none => false)

def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

/-- The ground closure checker (see the module header). -/
def checkGroundClosure (rules : List GroundRule) (facts : List String)
    (cert : GroundClosureCert) : Bool :=
  stratified rules && appsOK rules facts cert.applications &&
  saturated rules facts cert.applications &&
  closureOK rules facts cert.applications cert.closure &&
  nodupB (cert.applications.map (·.entry))

/-! ### Proofs -/

section
variable {rules : List GroundRule} {facts : List String}

theorem stage_eq (l : Nat) :
    Stage rules facts l = LayerReach rules (Below rules facts l) l := by
  cases l <;> rfl

theorem stage_succ {l : Nat} {a : String} (h : Stage rules facts l a) :
    Stage rules facts (l + 1) a :=
  LayerReach.base h

theorem stage_mono {l l' : Nat} (hl : l ≤ l') {a : String} (h : Stage rules facts l a) :
    Stage rules facts l' a := by
  induction l' with
  | zero => have : l = 0 := by omega
            subst this; exact h
  | succ n ih =>
    rcases Nat.lt_or_ge l (n + 1) with hlt | hge
    · exact stage_succ (ih (by omega))
    · have : l = n + 1 := by omega
      subst this; exact h

theorem facts_stage (l : Nat) {a : String} (h : a ∈ facts) : Stage rules facts l a := by
  induction l with
  | zero => exact LayerReach.base h
  | succ n ih => exact stage_succ ih

theorem below_stage (l : Nat) {a : String} (h : Below rules facts l a) :
    Stage rules facts l a := by
  rw [stage_eq]; exact LayerReach.base h

theorem below_of_stage {m l : Nat} (hm : m < l) {a : String} (h : Stage rules facts m a) :
    Below rules facts l a := by
  cases l with
  | zero => omega
  | succ n => exact stage_mono (by omega) h

theorem facts_below (l : Nat) {a : String} (h : a ∈ facts) : Below rules facts l a := by
  cases l with
  | zero => exact h
  | succ n => exact facts_stage n h

end

section
variable {rules : List GroundRule} {facts : List String} {apps : List GroundApplication}

theorem inUpTo_iff {l : Nat} {a : String} :
    inUpTo rules facts apps l a = true ↔
      a ∈ facts ∨ ∃ ap ∈ apps, ap.layer ≤ l ∧ conclOf rules ap = some a := by
  simp [inUpTo]

theorem inBelow_iff {l : Nat} {a : String} :
    inBelow rules facts apps l a = true ↔
      a ∈ facts ∨ ∃ ap ∈ apps, ap.layer < l ∧ conclOf rules ap = some a := by
  simp [inBelow]

/-- What `appOK` gives about one application. -/
structure AppFacts (rules : List GroundRule) (facts : List String)
    (apps : List GroundApplication) (k : Nat) (ap : GroundApplication) (r : GroundRule) : Prop where
  rule : rules[ap.entry]? = some r
  concl : ∃ c, r.conclusion = some c
  layer : ap.layer = r.layer
  defeat : ∀ d ∈ r.defeaters, ∃ x ∈ d, inBelow rules facts apps ap.layer x = false
  prem : ∀ p ∈ r.premises, p ∈ facts ∨ ∃ j < k, ∃ aj, apps[j]? = some aj ∧ conclOf rules aj = some p
  order : ∀ j < k, ∀ aj, apps[j]? = some aj → aj.layer ≤ ap.layer

theorem appOK_facts {k : Nat} {ap : GroundApplication} (h : appOK rules facts apps k ap = true) :
    ∃ r, AppFacts rules facts apps k ap r := by
  unfold appOK at h
  split at h
  · simp at h
  · rename_i r hr
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true',
      List.any_eq_true, Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hc, hl⟩, _⟩, _⟩, hd⟩, hp⟩, ho⟩ := h
    refine ⟨r, hr, Option.isSome_iff_exists.mp hc, hl, ?_, ?_, ?_⟩
    · intro d hdm
      have := hd d hdm
      simp only [List.all_eq_false] at this
      obtain ⟨x, hx, hn⟩ := this
      exact ⟨x, hx, by simpa using hn⟩
    · intro p hpm
      rcases hp p hpm with hf | ⟨aj, hj, he⟩
      · exact Or.inl hf
      · right
        obtain ⟨j, hget⟩ := List.mem_iff_getElem?.mp hj
        by_cases hjk : j < k
        · simp only [List.getElem?_take, hjk, ite_true] at hget
          exact ⟨j, hjk, aj, hget, he⟩
        · simp [List.getElem?_take, hjk] at hget
    · intro j hjk aj hget
      apply ho aj
      apply List.mem_iff_getElem?.mpr
      refine ⟨j, ?_⟩
      simp only [List.getElem?_take, hjk, ite_true]
      exact hget

theorem appsOK_at (h : appsOK rules facts apps = true) {k : Nat} {ap : GroundApplication}
    (hk : apps[k]? = some ap) : ∃ r, AppFacts rules facts apps k ap r := by
  have hlt : k < apps.length := by
    rcases List.getElem?_eq_some_iff.mp hk with ⟨hlt, _⟩; exact hlt
  have := List.all_eq_true.mp h k (List.mem_range.mpr hlt)
  rw [hk] at this
  exact appOK_facts this

theorem conclOf_some {ap : GroundApplication} {c : String} (h : conclOf rules ap = some c) :
    ∃ r, rules[ap.entry]? = some r ∧ r.conclusion = some c := by
  unfold conclOf at h
  split at h
  · rename_i r hr; exact ⟨r, hr, h⟩
  · simp at h

/-- The core induction: for every layer `l`, every application of layer `l`
concludes inside `Stage l` (soundness), and `Stage l` is inside the facts plus
the conclusions of applications of layer at most `l` (completeness). -/
theorem layer_correct (hs : appsOK rules facts apps = true)
    (hsat : saturated rules facts apps = true) :
    ∀ l, (∀ ap ∈ apps, ap.layer = l → ∀ c, conclOf rules ap = some c → Stage rules facts l c) ∧
      (∀ a, Stage rules facts l a → inUpTo rules facts apps l a = true) := by
  intro l
  induction l using Nat.strongRecOn with
  | _ l ih =>
  -- Below l, as the checker sees it, in both directions.
  have belowSound : ∀ a, inBelow rules facts apps l a = true → Below rules facts l a := by
    intro a ha
    rcases inBelow_iff.mp ha with hf | ⟨ap, hap, hlt, hc⟩
    · exact facts_below l hf
    · exact below_of_stage hlt ((ih ap.layer hlt).1 ap hap rfl a hc)
  have belowComplete : ∀ a, Below rules facts l a → inBelow rules facts apps l a = true := by
    intro a ha
    cases l with
    | zero => exact inBelow_iff.mpr (Or.inl ha)
    | succ n =>
      have := (ih n (by omega)).2 a ha
      rcases inUpTo_iff.mp this with hf | ⟨ap, hap, hle, hc⟩
      · exact inBelow_iff.mpr (Or.inl hf)
      · exact inBelow_iff.mpr (Or.inr ⟨ap, hap, by omega, hc⟩)
  have notFires : ∀ (d : List String),
      (∃ x ∈ d, inBelow rules facts apps l x = false) → ¬ Fires (Below rules facts l) d := by
    intro d ⟨x, hx, hn⟩ hf
    have := belowComplete x (hf x hx)
    rw [hn] at this; cases this
  -- Soundness at layer l, by strong induction on the position in the list.
  have sound : ∀ (k : Nat) (ap : GroundApplication), apps[k]? = some ap → ap.layer = l → ∀ c, conclOf rules ap = some c →
      Stage rules facts l c := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ihk =>
    intro ap hk hl c hc
    obtain ⟨r, hf⟩ := appsOK_at hs hk
    obtain ⟨r', hr', hrc⟩ := conclOf_some hc
    have hrr : r' = r := by rw [hf.rule] at hr'; exact (Option.some.inj hr').symm
    subst hrr
    rw [stage_eq]
    refine LayerReach.app (List.mem_of_getElem? hf.rule) (by rw [← hf.layer, hl]) hrc ?_ ?_
    · intro p hp
      rw [← stage_eq]
      rcases hf.prem p hp with hpf | ⟨j, hjk, aj, hj, hjc⟩
      · exact facts_stage l hpf
      · have hjl : aj.layer ≤ l := hl ▸ hf.order j hjk aj hj
        rcases Nat.lt_or_ge aj.layer l with hlt | hge
        · exact stage_mono (Nat.le_of_lt hlt) ((ih aj.layer hlt).1 aj (List.mem_of_getElem? hj) rfl p hjc)
        · exact ihk j hjk aj hj (by omega) p hjc
    · intro d hd
      exact notFires d (hl ▸ hf.defeat d hd)
  refine ⟨fun ap hap hl c hc => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hap
    exact sound k ap hk hl c hc
  -- Completeness at layer l, by induction on LayerReach.
  · intro a ha
    rw [stage_eq] at ha
    induction ha with
    | base hb =>
      rcases inBelow_iff.mp (belowComplete _ hb) with hf | ⟨ap, hap, hlt, hc⟩
      · exact inUpTo_iff.mpr (Or.inl hf)
      · exact inUpTo_iff.mpr (Or.inr ⟨ap, hap, Nat.le_of_lt hlt, hc⟩)
    | @app r a hr hrl hrc _ hdef ihp =>
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
      have hilt : i < rules.length := (List.getElem?_eq_some_iff.mp hi).1
      have happ : applicableB rules facts apps r = true := by
        simp only [applicableB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
        refine ⟨⟨by simp [hrc], fun p hp => hrl ▸ ihp p hp⟩, fun d hd => ?_⟩
        apply Bool.eq_false_iff.mpr
        intro hall
        apply hdef d hd
        intro x hx
        exact belowSound x (hrl ▸ (List.all_eq_true.mp hall x hx))
      have := List.all_eq_true.mp hsat i (List.mem_range.mpr hilt)
      rw [hi] at this
      simp only [happ, Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq] at this
      obtain ⟨ap, hap, hent⟩ := this
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hap
      obtain ⟨r2, hf⟩ := appsOK_at hs hk
      have hr2 : r2 = r := by
        have := hf.rule; rw [hent, hi] at this; exact (Option.some.inj this).symm
      subst hr2
      refine inUpTo_iff.mpr (Or.inr ⟨ap, hap, by rw [hf.layer, hrl]; exact Nat.le_refl _, ?_⟩)
      unfold conclOf; rw [hent, hi]; exact hrc

end

theorem maxLayer_ge {rules : List GroundRule} {r : GroundRule} (h : r ∈ rules) :
    r.layer ≤ maxLayer rules := by
  induction rules with
  | nil => simp at h
  | cons x xs ih =>
    show r.layer ≤ max x.layer (maxLayer xs)
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- **Ground closure exactness.** An accepted certificate's closure is exactly
the stratified defeasible closure, and the applications are exactly the
applicable rules. -/
theorem checkGroundClosure_exact {rules : List GroundRule} {facts : List String}
    {cert : GroundClosureCert} (h : checkGroundClosure rules facts cert = true) :
    (∀ a, a ∈ cert.closure ↔ GroundClosure rules facts a) ∧
    (∀ i r, rules[i]? = some r →
      ((∃ ap ∈ cert.applications, ap.entry = i) ↔ Applicable rules facts r)) := by
  simp only [checkGroundClosure, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, hs⟩, hsat⟩, hcl⟩, _⟩ := h
  have hc := layer_correct hs hsat
  -- every application concludes inside its own stage
  have appStage : ∀ ap ∈ cert.applications, ∀ c, conclOf rules ap = some c →
      Stage rules facts ap.layer c := fun ap hap c hcc => (hc ap.layer).1 ap hap rfl c hcc
  have appLayer : ∀ ap ∈ cert.applications, ∃ r, rules[ap.entry]? = some r ∧
      AppFacts rules facts cert.applications (cert.applications.idxOf ap) ap r := by
    intro ap hap
    have hk : cert.applications[cert.applications.idxOf ap]? = some ap := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨List.idxOf_lt_length_of_mem hap, List.getElem_idxOf (List.idxOf_lt_length_of_mem hap)⟩
    obtain ⟨r, hf⟩ := appsOK_at hs hk
    exact ⟨r, hf.rule, hf⟩
  simp only [closureOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem, List.any_eq_true, beq_iff_eq] at hcl
  obtain ⟨⟨hcl1, hcl2⟩, hcl3⟩ := hcl
  refine ⟨fun a => ⟨fun ha => ?_, fun ha => ?_⟩, fun i r hi => ⟨?_, ?_⟩⟩
  · rcases hcl1 a ha with hf | ⟨ap, hap, hca⟩
    · exact facts_stage _ hf
    · obtain ⟨r, hr, hf⟩ := appLayer ap hap
      have hrm := List.mem_of_getElem? hr
      exact stage_mono (hf.layer ▸ maxLayer_ge hrm) (appStage ap hap a hca)
  · rcases inUpTo_iff.mp ((hc _).2 a ha) with hf | ⟨ap, hap, _, hca⟩
    · exact hcl2 a hf
    · simpa [hca] using hcl3 ap hap
  · rintro ⟨ap, hap, rfl⟩
    obtain ⟨r', hr', hf⟩ := appLayer ap hap
    have : r' = r := by rw [hr'] at hi; exact Option.some.inj hi
    subst this
    refine ⟨hf.concl, fun p hp => ?_, fun d hd => ?_⟩
    · rcases hf.prem p hp with hpf | ⟨j, _, aj, hj, hjc⟩
      · exact facts_stage _ hpf
      · have hjm := List.mem_of_getElem? hj
        have hjl := hf.order j (by assumption) aj hj
        exact stage_mono (hf.layer ▸ hjl) (appStage aj hjm p hjc)
    · obtain ⟨x, hx, hn⟩ := hf.defeat d hd
      intro hfire
      -- the checker's Below and the semantics' Below agree (layer_correct)
      have hb := hfire x hx
      rw [← hf.layer] at hb
      have : inBelow rules facts cert.applications ap.layer x = true := by
        cases hl : ap.layer with
        | zero => rw [hl] at hb; exact inBelow_iff.mpr (Or.inl hb)
        | succ n =>
          rw [hl] at hb
          rcases inUpTo_iff.mp ((hc n).2 x hb) with hf' | ⟨aj, haj, hle, hjc⟩
          · exact inBelow_iff.mpr (Or.inl hf')
          · exact inBelow_iff.mpr (Or.inr ⟨aj, haj, by omega, hjc⟩)
      rw [hn] at this; cases this
  · rintro ⟨⟨c, hcr⟩, hp, hd⟩
    have hilt : i < rules.length := (List.getElem?_eq_some_iff.mp hi).1
    have happ : applicableB rules facts cert.applications r = true := by
      simp only [applicableB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
      refine ⟨⟨by simp [hcr], fun p hpm => (hc r.layer).2 p (hp p hpm)⟩, fun d hdm => ?_⟩
      apply Bool.eq_false_iff.mpr
      intro hall
      apply hd d hdm
      intro x hx
      have hxb := List.all_eq_true.mp hall x hx
      rcases inBelow_iff.mp hxb with hf | ⟨aj, haj, hlt, hjc⟩
      · exact facts_below _ hf
      · exact below_of_stage hlt (appStage aj haj x hjc)
    have := List.all_eq_true.mp hsat i (List.mem_range.mpr hilt)
    rw [hi] at this
    simp only [happ, Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq] at this
    exact this

/-- **Ground closure soundness**: every atom of an accepted closure is in the
stratified defeasible closure. -/
theorem checkGroundClosure_sound {rules : List GroundRule} {facts : List String}
    {cert : GroundClosureCert} (h : checkGroundClosure rules facts cert = true) :
    ∀ atom ∈ cert.closure, GroundClosure rules facts atom :=
  fun a ha => ((checkGroundClosure_exact h).1 a).mp ha

end NMMS
