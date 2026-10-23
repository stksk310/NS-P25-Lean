import NS25Lean.P2SectorCHerzogCanonicalityOwnerReentryR6

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR7

open L5A2C4H L5A2C4K L5A2C4L L5A2C4OR1 L5A2C4OR2

variable {Gamma : NumericalSemigroup}

private noncomputable instance routingANeZero
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩

private theorem wordLegal_get_step
    {R : Type*} [Fintype R] (D : CombinatorialCore.ResidueData R)
    {start : R} {word : List L5A2C4K.ResidueData.RawDirection}
    (hlegal : L5A2C4K.ResidueData.WordLegal D start word)
    (k : ℕ) (hk : k < word.length) :
    let d := word[k]
    L5A2C4K.ResidueData.LegalEdge D d
        (L5A2C4K.ResidueData.follow D start (word.take k)) ∧
      L5A2C4K.ResidueData.follow D start (word.take (k + 1)) =
        L5A2C4K.ResidueData.step D d
          (L5A2C4K.ResidueData.follow D start (word.take k)) := by
  induction word generalizing start k with
  | nil => simp at hk
  | cons d word ih =>
      rcases hlegal with ⟨hd, hword⟩
      cases k with
      | zero => simpa [L5A2C4K.ResidueData.follow]
      | succ k =>
          have hk' : k < word.length := by simpa using hk
          simpa [L5A2C4K.ResidueData.follow] using
            (ih (start := L5A2C4K.ResidueData.step D d start)
              hword k hk')

/-- A source-exact adjacent transition.  Its fields are only actual decorated
history data, an in-range station, a translation amount, and the literal
equality between the actual child state and the translated parent state. -/
structure ActualOwnerSelectorTransition
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) where
  rooted : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e)
  station : ℕ
  station_lt : station <
    L5A2C4K.ResidueData.RawHistory.length (routingData B e) rooted.raw
  translation : ℕ
  translated_child :
    L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) rooted.raw
        (station + 1) =
      L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) rooted.raw
          station - (translation * routingM B e : ℕ)

def transitionDirection
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (T : ActualOwnerSelectorTransition B e) :
    L5A2C4K.ResidueData.RawDirection :=
  T.rooted.raw.word[T.station]'(by
    simpa [L5A2C4K.ResidueData.RawHistory.length] using T.station_lt)

def transitionParent
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (T : ActualOwnerSelectorTransition B e) : ZMod (routingA B e) :=
  L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) T.rooted.raw T.station

def transitionChild
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (T : ActualOwnerSelectorTransition B e) : ZMod (routingA B e) :=
  L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) T.rooted.raw
    (T.station + 1)

/-- The certificate's adjacent states really are joined by the next legal
edge of its actual raw history. -/
theorem actual_transition_edge
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (T : ActualOwnerSelectorTransition B e) :
    L5A2C4K.ResidueData.LegalEdge (routingData B e)
        (transitionDirection B e T) (transitionParent B e T) ∧
      transitionChild B e T =
        L5A2C4K.ResidueData.step (routingData B e)
          (transitionDirection B e T) (transitionParent B e T) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  simpa [transitionDirection, transitionParent, transitionChild,
    L5A2C4K.ResidueData.RawHistory.stateAt,
    L5A2C4K.ResidueData.RawHistory.length] using
    (wordLegal_get_step (routingData B e) T.rooted.raw.legal
      T.station T.station_lt)

/-- Actual owner-selector transport.  The conclusion is not stored in the
certificate: it is the frozen relative MAX-MIN theorem applied to its literal
translated-state equality.  Greatest-minimizer tie breaking is retained. -/
theorem actual_owner_selector_transition
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (T : ActualOwnerSelectorTransition B e) {p : ℕ}
    (hq : 0 < T.translation) (hqp : T.translation < p)
    (hp : p = currentSelector B e (transitionParent B e T)) :
    p - T.translation = currentSelector B e (transitionChild B e T) := by
  unfold transitionChild
  rw [T.translated_child]
  exact relativeMaxMin_selector_difference B e (transitionParent B e T)
    hq hqp hp

/-- Source-hit/reset version of the raw-fact certificate. -/
structure ActualSourceHitOwnerTransition
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) where
  incoming : L5A2C4K.ResidueData.RawHistory (routingData B e)
  target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e)
  hit : L5A2C4K.ResidueData.SourceHit (routingData B e) incoming target.raw
  station : ℕ
  station_le : station ≤
    L5A2C4K.ResidueData.RawHistory.length (routingData B e) incoming
  translation : ℕ
  translated_reset :
    (L5A2C4L.ResidueData.sourceHitReset (routingData B e)
      incoming target hit).raw.start =
      L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) incoming station -
        (translation * routingM B e : ℕ)

/-- Source-hit reset preserves its actual package and legality, while its
literal translated start transports MAX-MIN exactly as in the adjacent case. -/
theorem actual_sourceHit_owner_selector_transition
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (T : ActualSourceHitOwnerTransition B e) {p : ℕ}
    (hq : 0 < T.translation) (hqp : T.translation < p)
    (hp : p = currentSelector B e
      (L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e)
        T.incoming T.station)) :
    p - T.translation = currentSelector B e
      (L5A2C4L.ResidueData.sourceHitReset (routingData B e)
        T.incoming T.target T.hit).raw.start := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  rw [T.translated_reset]
  exact relativeMaxMin_selector_difference B e _ hq hqp hp

theorem actual_sourceHit_owner_selector_transition_spec
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (T : ActualSourceHitOwnerTransition B e) {p : ℕ}
    (hq : 0 < T.translation) (hqp : T.translation < p)
    (hp : p = currentSelector B e
      (L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e)
        T.incoming T.station)) :
    let reset := L5A2C4L.ResidueData.sourceHitReset (routingData B e)
      T.incoming T.target T.hit
    reset.package = T.target.package ∧
      reset.raw.start = T.target.package.val ∧
      L5A2C4K.ResidueData.RawHistory.endpoint (routingData B e) reset.raw =
        L5A2C4K.ResidueData.RawHistory.endpoint (routingData B e) T.incoming ∧
      L5A2C4K.ResidueData.WordLegal (routingData B e)
        reset.raw.start reset.raw.word ∧
      p - T.translation = currentSelector B e reset.raw.start := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  exact ⟨rfl,
    L5A2C4L.ResidueData.sourceHitReset_start (routingData B e)
      T.incoming T.target T.hit,
    L5A2C4L.ResidueData.sourceHitReset_endpoint (routingData B e)
      T.incoming T.target T.hit,
    L5A2C4L.ResidueData.sourceHitReset_legal (routingData B e)
      T.incoming T.target T.hit,
    actual_sourceHit_owner_selector_transition B e T hq hqp hp⟩

/-- Literal decorated replay transports the actual MAX-MIN selector only
because it supplies literal raw state equality in addition to package equality. -/
theorem literalDecoratedReplay_currentSelector
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {H₁ H₂ : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e)}
    (h : L5A2C4L.ResidueData.LiteralDecoratedReplay (routingData B e) H₁ H₂)
    (k : ℕ) :
    currentSelector B e
        (L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) H₁.raw k) =
    currentSelector B e
        (L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) H₂.raw k) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  apply congrArg (currentSelector B e)
  exact L5A2C4K.ResidueData.literalRawReplay_stateAt (routingData B e) h.2 k

theorem literalDecoratedReplay_owner_state
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {H₁ H₂ : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e)}
    (h : L5A2C4L.ResidueData.LiteralDecoratedReplay (routingData B e) H₁ H₂) :
    H₁.package = H₂.package ∧
      L5A2C4K.ResidueData.LiteralRawReplay (routingData B e) H₁.raw H₂.raw ∧
      ∀ k, currentSelector B e
          (L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) H₁.raw k) =
        currentSelector B e
          (L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) H₂.raw k) := by
  exact ⟨h.1, h.2, fun k => literalDecoratedReplay_currentSelector B e h k⟩

/-- Frozen activity/floor calculus specialized to the actual parent/child
states named by an R7 transition. -/
theorem actual_transition_activity_floor
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (T : ActualOwnerSelectorTransition B e) {p : ℕ}
    (hq : 0 < T.translation)
    (hqmin : rawCandidate B e T.translation (transitionParent B e T) =
      rawMinimum B e (transitionParent B e T))
    (hp : p = currentSelector B e (transitionParent B e T)) :
    (T.translation = p ↔ 0 < rawMinimum B e (transitionChild B e T)) ∧
      (T.translation < p ↔ rawMinimum B e (transitionChild B e T) = 0) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  unfold transitionChild
  rw [T.translated_child]
  exact ⟨rawActivity_iff B e _ hq hqmin hp,
    rawFloor_iff B e _ hq hqmin hp⟩

/-- If the translated amount is the actual MAX-MIN owner at the parent, the
actual child is its strictly positive UMSP shadow. -/
theorem actual_transition_umsp
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (T : ActualOwnerSelectorTransition B e)
    (howner : T.translation =
      currentSelector B e (transitionParent B e T)) :
    0 < rawMinimum B e (transitionChild B e T) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  unfold transitionChild
  rw [T.translated_child, howner]
  exact rawUMSP B e (transitionParent B e T)

/-- Every actual exceptional source branch has a canonical zero-length,
source-rooted legal history.  No terminal outcome is attached to it. -/
noncomputable def exceptionalBranchRootedHistory
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e)) :
    L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e) where
  package := s.val
  raw := {
    start := s.val.val
    word := []
    legal := by trivial }
  start_eq := rfl

/-- The rooted exceptional source starts with the actual MAX-MIN owner data,
including its retained Min-set membership; no unique minimizer is asserted. -/
theorem exceptionalBranch_initial_owner_state
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e)) :
    let H := exceptionalBranchRootedHistory B e s
    let r := L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) H.raw 0
    let q := currentSelector B e r
    r = s.val.val ∧
      0 < q ∧ q ∈ RawMinimizers B e r ∧
        rawCandidate B e q r = rawMinimum B e r := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp [exceptionalBranchRootedHistory]
  exact ⟨rfl, currentSelector_pos B e _, currentSelector_mem B e _,
    rawCandidate_currentSelector B e _⟩

end NS25Lean.L5A2C4OR7
