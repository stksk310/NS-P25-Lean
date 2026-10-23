import NS25Lean.P3PrefixRoutingR60
import NS25Lean.P2SectorCPhysicalHeightBridge

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R62
open FourGeneratedBridge ChosenBase L5A2C4H L5A2C4OR1 L5A2C4OR3 L5A2B4AR1 L5A2BFinalRepair
variable {Gamma : NumericalSemigroup}

/-- Actual routing carrier, with the original pivot as return parameter. -/
theorem routingI_carrier_eq_finalCarrier (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (routingI B e).carrier = finalCarrier (routingH B e) B.q.val
      (principalIndex (routingH B e) B.q.val B.q_positive) := by
  rw [← positiveReturnCarrier_eq_finalCarrier]
  ext z
  simpa [positiveReturnCarrier, mem_returnIdeal_iff, routingM, Nat.cast_mul]
    using mem_routingI_iff_positive_return B e z

theorem completed_birthIdeal_carrier (H : NumericalSemigroup) (m Q : ℕ)
    (hQ : 1 < Q) :
    (P3R60.birthIdeal H m (Q-1) (by omega)).carrier = prefixCarrier H m Q := by
  rw [P3R60.birthIdeal_carrier, Nat.sub_add_cancel (by omega : 1 ≤ Q)]

theorem prefixCarrier_one (H : NumericalSemigroup) (m : ℕ) :
    prefixCarrier H m 1 = ∅ := by
  ext z
  simp only [mem_prefixCarrier_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨q, hq, hq1, _⟩
  omega

theorem prefixCarrier_two (H : NumericalSemigroup) (m : ℕ) :
    prefixCarrier H m 2 = (returnIdeal H m).carrier := by
  ext z
  constructor
  · rintro ⟨q, hq, hq2, hz⟩
    have he : q = 1 := by omega
    simpa [he] using hz
  · intro hz
    exact ⟨1, by omega, by omega, by simpa using hz⟩

theorem routingI_eq_principal_translate_of_index_one
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hQ : principalIndex (routingH B e) B.q.val B.q_positive = 1) :
    routingI B e = (routingH B e).asRelativeIdeal.translate B.q.val := by
  apply RelativeIdeal.ext
  intro z
  change z ∈ (routingI B e).carrier ↔ _
  rw [routingI_carrier_eq_finalCarrier, hQ]
  simp [finalCarrier, prefixCarrier_one]

theorem routing_principal_not_mem_prefix (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    ((principalIndex (routingH B e) B.q.val B.q_positive * B.q.val : ℕ) : ℤ) ∉
      prefixCarrier (routingH B e) B.q.val
        (principalIndex (routingH B e) B.q.val B.q_positive) :=
  principal_not_mem_prefix _ _ _

theorem routing_principal_isMinimalGenerator (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (routingI B e).IsMinimalGenerator
      (principalIndex (routingH B e) B.q.val B.q_positive * B.q.val : ℕ) := by
  change IsSource (routingH B e) (routingI B e).carrier _
  rw [routingI_carrier_eq_finalCarrier]
  exact principal_is_new_source _ _ _

/-- Only minimal sources, without a claim of source-target persistence. -/
theorem routing_old_source_is_completed_source (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH B e) B.q.val B.q_positive)
    (s : ℤ) (hs : (routingI B e).IsMinimalGenerator s)
    (hne : s ≠ (principalIndex (routingH B e) B.q.val B.q_positive * B.q.val : ℕ)) :
    (P3R60.birthIdeal (routingH B e) B.q.val
      (principalIndex (routingH B e) B.q.val B.q_positive - 1) (by omega)).IsMinimalGenerator s := by
  change IsSource (routingH B e) (routingI B e).carrier s at hs
  rw [routingI_carrier_eq_finalCarrier] at hs
  change IsSource (routingH B e) _ s
  rw [completed_birthIdeal_carrier _ _ _ hQ]
  exact branchBirth_isPrefixSource ⟨hs, hne⟩

/-- Exact survival criterion for a nonprincipal prefix source. -/
theorem routing_old_source_survives_iff (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ℤ)
    (hne : s ≠ (principalIndex (routingH B e) B.q.val B.q_positive * B.q.val : ℕ)) :
    (routingI B e).IsMinimalGenerator s ↔
      IsSource (routingH B e)
        (prefixCarrier (routingH B e) B.q.val
          (principalIndex (routingH B e) B.q.val B.q_positive)) s ∧
      ∀ t : ℕ, t ∈ routingH B e → t ≠ 0 →
        s - t ∉ ((routingH B e).asRelativeIdeal.translate
          (principalIndex (routingH B e) B.q.val B.q_positive * B.q.val)).carrier := by
  change IsSource (routingH B e) (routingI B e).carrier s ↔ _
  rw [routingI_carrier_eq_finalCarrier]
  constructor
  · intro hs
    refine ⟨branchBirth_isPrefixSource ⟨hs, hne⟩, ?_⟩
    intro t ht ht0 hsub
    exact hs.2 t ht ht0 (Or.inr hsub)
  · rintro ⟨hs, hex⟩
    refine ⟨Or.inl hs.1, ?_⟩
    intro t ht ht0 hsub
    rcases hsub with hp | hprincipal
    · exact hs.2 t ht ht0 hp
    · exact hex t ht ht0 hprincipal

/-- Actual graph sources represent the minimal routing generators. -/
theorem routing_source_iff_minimal (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ∀ r : ZMod (routingA B e), (routingData B e).IsSource r ↔
      (routingI B e).IsMinimalGenerator ((routingI B e).aperyRepresentative (routingA B e) r) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hmin := normalizedSemigroup_minimal (chosenBase_minimalFour B e)
  have hb : routingB B e ≠ 0 := by
    intro hz
    apply hmin.2.2.1
    simpa only [routingB, hz] using (AddSubmonoid.zero_mem _)
  have hc : routingC B e ≠ 0 := by
    intro hz
    apply hmin.2.2.2
    simpa only [routingC, hz] using (AddSubmonoid.zero_mem _)
  intro r
  exact (routingI B e).concrete_isSource_iff_isMinimalGenerator
    (routingA B e) (routingB B e) (routingC B e) hmin.1
    (routingHB B e) (routingHC B e) hb hc r

/-- Final raw graph sources other than the principal representative
are sources of the completed carrier; no source-target statement is made. -/
theorem routing_old_raw_source_is_completed_source (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH B e) B.q.val B.q_positive) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ∀ r : ZMod (routingA B e), (routingData B e).IsSource r →
      (routingI B e).aperyRepresentative (routingA B e) r ≠
        (principalIndex (routingH B e) B.q.val B.q_positive * B.q.val : ℕ) →
      (P3R60.birthIdeal (routingH B e) B.q.val
        (principalIndex (routingH B e) B.q.val B.q_positive - 1)
        (by omega)).IsMinimalGenerator
        ((routingI B e).aperyRepresentative (routingA B e) r) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  intro r hs hne
  exact routing_old_source_is_completed_source B e hQ _
    ((routing_source_iff_minimal B e r).mp hs) hne

theorem routing_completed_birthIdeal_carrier (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH B e) B.q.val B.q_positive) :
    (P3R60.birthIdeal (routingH B e) B.q.val
      (principalIndex (routingH B e) B.q.val B.q_positive - 1) (by omega)).carrier =
    prefixCarrier (routingH B e) B.q.val
      (principalIndex (routingH B e) B.q.val B.q_positive) :=
  completed_birthIdeal_carrier _ _ _ hQ

theorem routingI_carrier_eq_completed_union_principal (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH B e) B.q.val B.q_positive) :
    (routingI B e).carrier =
      (P3R60.birthIdeal (routingH B e) B.q.val
        (principalIndex (routingH B e) B.q.val B.q_positive - 1) (by omega)).carrier ∪
      ((routingH B e).asRelativeIdeal.translate
        (principalIndex (routingH B e) B.q.val B.q_positive * B.q.val)).carrier := by
  rw [routing_completed_birthIdeal_carrier B e hQ, routingI_carrier_eq_finalCarrier]
  rfl

theorem routing_principal_is_raw_source (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingData B e).IsSource
      ((principalIndex (routingH B e) B.q.val B.q_positive * B.q.val : ℕ) : ZMod (routingA B e)) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hp := routing_principal_isMinimalGenerator B e
  have hmin := normalizedSemigroup_minimal (chosenBase_minimalFour B e)
  have he := (routingI B e).aperyRepresentative_eq_of_isMinimalGenerator
    (routingA B e) (routingB B e) (routingC B e) hmin.1 hp
  apply (routing_source_iff_minimal B e _).mpr
  have he2 := he
  simp only [Int.cast_natCast] at he2
  rw [he2]
  exact hp

/-- At the same residue, every surviving old final raw source is a
completed-prefix raw source. This concerns sources only, not cross edges. -/
theorem routing_old_raw_source_is_completed_raw_source (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH B e) B.q.val B.q_positive) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ∀ r : ZMod (routingA B e), (routingData B e).IsSource r →
      (routingI B e).aperyRepresentative (routingA B e) r ≠
        (principalIndex (routingH B e) B.q.val B.q_positive * B.q.val : ℕ) →
      (P3R60.idealData
        (P3R60.birthIdeal (routingH B e) B.q.val
          (principalIndex (routingH B e) B.q.val B.q_positive - 1) (by omega))
        (routingA B e) (routingB B e) (routingC B e)
        (routingHB B e) (routingHC B e)).IsSource r := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  intro r hs hne
  let I := P3R60.birthIdeal (routingH B e) B.q.val
    (principalIndex (routingH B e) B.q.val B.q_positive - 1) (by omega)
  have hmin := normalizedSemigroup_minimal (chosenBase_minimalFour B e)
  have hb : routingB B e ≠ 0 := by
    intro hz
    apply hmin.2.2.1
    simpa only [routingB, hz] using (AddSubmonoid.zero_mem _)
  have hc : routingC B e ≠ 0 := by
    intro hz
    apply hmin.2.2.2
    simpa only [routingC, hz] using (AddSubmonoid.zero_mem _)
  have hm : I.IsMinimalGenerator ((routingI B e).aperyRepresentative (routingA B e) r) :=
    routing_old_raw_source_is_completed_source B e hQ r hs hne
  have he := I.aperyRepresentative_eq_of_isMinimalGenerator
    (routingA B e) (routingB B e) (routingC B e) hmin.1 hm
  rw [(routingI B e).aperyRepresentative_mod] at he
  apply (I.concrete_isSource_iff_isMinimalGenerator
    (routingA B e) (routingB B e) (routingC B e) hmin.1
    (routingHB B e) (routingHC B e) hb hc r).mpr
  rw [he]
  exact hm

end NS25Lean.P3R62






