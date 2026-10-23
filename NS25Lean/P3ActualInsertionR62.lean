import NS25Lean.P3PrincipalInsertionR62
import NS25Lean.P3InsertionAperyR62
import NS25Lean.P3G3SupportR61

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R62
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4I L5A2B4AR1
variable {Gamma : NumericalSemigroup}

theorem routingI_eq_inserted_ideal (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH B e) B.q.val B.q_positive) :
    routingI B e = idealUnion
      (P3R60.birthIdeal (routingH B e) B.q.val
        (principalIndex (routingH B e) B.q.val B.q_positive-1) (by omega))
      ((routingH B e).asRelativeIdeal.translate
        (principalIndex (routingH B e) B.q.val B.q_positive*B.q.val)) := by
  apply RelativeIdeal.ext
  intro x
  change x ∈ (routingI B e).carrier ↔ _
  rw [routingI_carrier_eq_finalCarrier]
  change (x ∈ prefixCarrier (routingH B e) B.q.val
      (principalIndex (routingH B e) B.q.val B.q_positive) ∨
      x-(principalIndex (routingH B e) B.q.val B.q_positive*B.q.val : ℕ) ∈ (routingH B e).asRelativeIdeal) ↔
    (x ∈ (P3R60.birthIdeal (routingH B e) B.q.val
      (principalIndex (routingH B e) B.q.val B.q_positive-1) (by omega)).carrier ∨
      x-(principalIndex (routingH B e) B.q.val B.q_positive*B.q.val : ℕ) ∈ (routingH B e).asRelativeIdeal)
  rw [completed_birthIdeal_carrier _ _ _ hQ]

theorem routing_apery_principal_min (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH B e) B.q.val B.q_positive) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let Q := principalIndex (routingH B e) B.q.val B.q_positive
    let I := P3R60.birthIdeal (routingH B e) B.q.val (Q-1) (by omega)
    ∀ s : ZMod (routingA B e),
      (routingI B e).aperyRepresentative (routingA B e) s =
        min (I.aperyRepresentative (routingA B e) s)
          ((Q*B.q.val : ℕ)+(routingH B e).asRelativeIdeal.aperyRepresentative
            (routingA B e) (s-((Q*B.q.val : ℕ) : ZMod (routingA B e)))) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro s
  rw [routingI_eq_inserted_ideal B e hQ,principal_union_aperyRepresentative]
  simp only [Nat.cast_mul,Int.cast_mul,Int.cast_natCast]

theorem routing_step_principal_update (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH B e) B.q.val B.q_positive) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let Q := principalIndex (routingH B e) B.q.val B.q_positive
    let I := P3R60.birthIdeal (routingH B e) B.q.val (Q-1) (by omega)
    let J := (routingH B e).asRelativeIdeal.translate (Q*B.q.val)
    ∀ h : ℕ, ∀ hh : h ∈ routingH B e, ∀ s : ZMod (routingA B e),
      ((routingI B e).aperyStepQuotient (routingA B e) h hh s : ℤ) =
        (I.aperyStepQuotient (routingA B e) h hh s : ℤ)-
          insertionDrop I J (routingA B e) s+insertionDrop I J (routingA B e) (s+h) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro h hh s
  rw [routingI_eq_inserted_ideal B e hQ]
  exact insertion_step_eq _ _ _ _ hh s

theorem routing_old_raw_source_preserves_target_rep (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH B e) B.q.val B.q_positive) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let I := P3R60.birthIdeal (routingH B e) B.q.val
      (principalIndex (routingH B e) B.q.val B.q_positive-1) (by omega)
    ∀ r : ZMod (routingA B e), (routingData B e).IsSource r →
      (routingI B e).aperyRepresentative (routingA B e) r ≠
        (principalIndex (routingH B e) B.q.val B.q_positive*B.q.val : ℕ) →
      I.aperyRepresentative (routingA B e) r = (routingI B e).aperyRepresentative (routingA B e) r := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro r hs hne
  let I := P3R60.birthIdeal (routingH B e) B.q.val
    (principalIndex (routingH B e) B.q.val B.q_positive-1) (by omega)
  have hmin := routing_old_raw_source_is_completed_source B e hQ r hs hne
  have he := I.aperyRepresentative_eq_of_isMinimalGenerator (routingA B e)
    (routingB B e) (routingC B e) (by rfl) hmin
  rw [(routingI B e).aperyRepresentative_mod] at he
  exact he

end NS25Lean.P3R62
