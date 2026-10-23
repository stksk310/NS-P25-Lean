import NS25Lean.P3RecordGeometryR60

set_option linter.style.header false
set_option maxHeartbeats 800000
noncomputable section
namespace NS25Lean.P3R61
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2B4AR1
variable {Gamma : NumericalSemigroup}

/-- In the critical rectangle an a-free factorization is unique, even among
unbounded nonnegative alternative coordinates. -/
theorem subcritical_bc_factorization_unique (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j i' j' : ℕ) (hi : i < criticalExponent B (e 1))
    (hj : j < criticalExponent B (e 2))
    (he : (i : ℤ)*routingB B e+j*routingC B e =
      (i' : ℤ)*routingB B e+j'*routingC B e) : i = i' ∧ j = j' := by
  have heN : i*routingB B e+j*routingC B e =
      i'*routingB B e+j'*routingC B e := by exact_mod_cast he
  obtain ⟨ha, hb, hc⟩ := P3R58.routing_scale_weights B e
  have heW : i*weights B (e 1)+j*weights B (e 2) =
      i'*weights B (e 1)+j'*weights B (e 2) := by
    rw [← hb, ← hc]
    nlinarith only [congrArg (fun n : ℕ => routingD B e*n) heN]
  have hbp := weights_positive B (e 1)
  have hcp := weights_positive B (e 2)
  have hii : i = i' := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hjlt : j' < j := by nlinarith only [heW, hlt, hbp, hcp]
      have hrel : (j-j')*weights B (e 2) =
          0*weights B (e 0)+(i'-i)*weights B (e 1) := by
        have hs := Nat.sub_add_cancel (le_of_lt hjlt)
        have ht := Nat.sub_add_cancel (le_of_lt hlt)
        nlinarith only [heW, hs, ht]
      have hm := P3R57.critical_pair_minimum B (e 2) (e 0) (e 1)
        (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (j-j') 0 (i'-i) (Nat.sub_pos_of_lt hjlt) hrel
      omega
    · have hjlt : j < j' := by nlinarith only [heW, hgt, hbp, hcp]
      have hrel : (i-i')*weights B (e 1) =
          0*weights B (e 0)+(j'-j)*weights B (e 2) := by
        have hs := Nat.sub_add_cancel (le_of_lt hgt)
        have ht := Nat.sub_add_cancel (le_of_lt hjlt)
        nlinarith only [heW, hs, ht]
      have hm := P3R57.critical_pair_minimum B (e 1) (e 0) (e 2)
        (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (i-i') 0 (j'-j) (Nat.sub_pos_of_lt hgt) hrel
      omega
  exact ⟨hii, by rw [hii] at heW; nlinarith only [heW, hcp]⟩

/-- An actual semigroup Apéry value cannot have a positive a coefficient. -/
theorem canonical_factorization_a_eq_zero (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (alpha : ℤ) (A B' C : ℕ) (hcan : P3R60.CanonicalValue B e alpha)
    (he : alpha = (A : ℤ)*routingA B e+B'*routingB B e+C*routingC B e) :
    A = 0 := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  by_contra hn
  have hA : 1 ≤ A := by omega
  have hm : (A-1)*routingA B e+B'*routingB B e+C*routingC B e ∈ routingH B e := by
    change _ ∈ generatedThree (routingA B e) (routingB B e) (routingC B e)
    exact (mem_generatedThree_iff _ _ _ _).mpr ⟨A-1, B', C, rfl⟩
  have hnot := (routingH B e).asRelativeIdeal.aperyRepresentative_sub_modulus_not_mem
    (routingA B e) (alpha : ZMod (routingA B e))
  change physicalAlpha B e (alpha : ZMod (routingA B e))-routingA B e ∉
    (routingH B e).asRelativeIdeal at hnot
  rw [hcan] at hnot
  apply hnot
  refine ⟨_, hm, ?_⟩
  rw [he]
  push_cast
  rw [Nat.cast_sub hA]
  push_cast
  ring

/-- Coordinatewise divisibility of a canonical cell by an explicit a-free
weight. The residual is membership in the actual normalized semigroup. -/
theorem canonical_residual_coordinates (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j x y : ℕ) (hi : i < criticalExponent B (e 1))
    (hj : j < criticalExponent B (e 2))
    (hcan : P3R60.CanonicalValue B e ((i : ℤ)*routingB B e+j*routingC B e))
    (hres : (i : ℤ)*routingB B e+j*routingC B e-
      ((x : ℤ)*routingB B e+y*routingC B e) ∈ (routingH B e).asRelativeIdeal) :
    x ≤ i ∧ y ≤ j := by
  obtain ⟨n, hn, he⟩ := hres
  obtain ⟨A, B', C, hf⟩ := L5A2C4OR6.routingH_factorization B e hn
  have hdecomp : (i : ℤ)*routingB B e+j*routingC B e =
      (A : ℤ)*routingA B e+(x+B' : ℕ)*routingB B e+(y+C : ℕ)*routingC B e := by
    rw [hf] at he
    push_cast at he ⊢
    linarith
  have hA := canonical_factorization_a_eq_zero B e _ A (x+B') (y+C) hcan hdecomp
  rw [hA, Nat.cast_zero, zero_mul, zero_add] at hdecomp
  obtain ⟨hI, hJ⟩ := subcritical_bc_factorization_unique B e i j (x+B') (y+C) hi hj hdecomp
  omega

end NS25Lean.P3R61


