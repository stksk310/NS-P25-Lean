import NS25Lean.DilationBoundary

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase
variable {Gamma : NumericalSemigroup}

theorem dilated_minimal (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) (i : Fin 4) :
    dilatedDegrees B D i ∉ AddSubmonoid.closure (dilatedDegrees B D '' {j | j ≠ i}) := by
  have hDpos : 0 < D := lt_trans B.q_positive hD
  refine Fin.cases ?_ (fun k => ?_) i
  · intro hm
    have hdiv : D ∣ dilatedDegrees B D 0 := by
      generalize he : dilatedDegrees B D 0 = n at hm ⊢
      clear he
      induction hm using AddSubmonoid.closure_induction with
      | mem x hx =>
          obtain ⟨j, hj, rfl⟩ := hx
          obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
          exact dvd_mul_right _ _
      | zero => exact dvd_zero _
      | add a b ha hb iha ihb => exact dvd_add iha ihb
    exact (Nat.not_le.mpr hD) (Nat.le_of_dvd B.q_positive hdiv)
  · intro hm
    let G : AddSubmonoid ℕ := AddSubmonoid.closure (weights B '' {j | j ≠ k})
    have hex : ∃ r g : ℕ, g ∈ G ∧ D * weights B k = r * B.q.val + D * g := by
      change ∃ r g : ℕ, g ∈ G ∧ dilatedDegrees B D k.succ = r * B.q.val + D * g
      generalize he : dilatedDegrees B D k.succ = n at hm ⊢
      clear he
      induction hm using AddSubmonoid.closure_induction with
      | mem x hx =>
          obtain ⟨j, hj, rfl⟩ := hx
          revert hj
          refine Fin.cases ?_ (fun l => ?_) j
          · intro hj
            exact ⟨1, 0, G.zero_mem, by simp [dilatedDegrees]⟩
          · intro hj
            refine ⟨0, weights B l, AddSubmonoid.subset_closure ⟨l, ?_, rfl⟩, by simp [dilatedDegrees]⟩
            intro he
            exact hj (congrArg Fin.succ he)
      | zero => exact ⟨0, 0, G.zero_mem, by simp⟩
      | add a b ha hb iha ihb =>
          obtain ⟨r, g, hg, he⟩ := iha
          obtain ⟨s, f, hf, he'⟩ := ihb
          exact ⟨r + s, g + f, G.add_mem hg hf, by rw [he, he']; ring⟩
    obtain ⟨r, g, hg, he⟩ := hex
    have hdiv : D ∣ r * B.q.val := by
      have ht := Nat.dvd_sub (dvd_mul_right D (weights B k)) (dvd_mul_right D g)
      have he' : D * weights B k - D * g = r * B.q.val := by omega
      exact he' ▸ ht
    obtain ⟨l, hl⟩ := hcop.dvd_of_dvd_mul_right hdiv
    have he' : weights B k = l * B.q.val + g := by
      apply Nat.eq_of_mul_eq_mul_left hDpos
      calc
        D * weights B k = r * B.q.val + D * g := he
        _ = D * (l * B.q.val + g) := by rw [hl]; ring
    apply B.degrees_minimal k.succ
    change weights B k ∈ _
    rw [he']
    have hq : B.q.val ∈ AddSubmonoid.closure
        ((fun j => (B.degrees j).val) '' {j | j ≠ k.succ}) := by
      exact AddSubmonoid.subset_closure ⟨0, (Fin.succ_ne_zero k).symm, by simp⟩
    have hgle : G ≤ AddSubmonoid.closure ((fun j => (B.degrees j).val) '' {j | j ≠ k.succ}) := by
      apply AddSubmonoid.closure_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      exact AddSubmonoid.subset_closure ⟨j.succ, fun he => hj (Fin.succ_inj.mp he), rfl⟩
    exact AddSubmonoid.add_mem _ (by simpa [nsmul_eq_mul] using
      (AddSubmonoid.closure ((fun j => (B.degrees j).val) '' {j | j ≠ k.succ})).nsmul_mem hq l)
      (hgle hg)

def dilatedData (B : Data Gamma) (D : ℕ) (hD : B.q.val < D) (hcop : Nat.Coprime D B.q.val) :
    Data (dilatedSemigroup B D hcop) where
  family i := ⟨dilatedDegrees B D i, by
    change dilatedDegrees B D i ∈ dilatedMonoid B D
    rw [dilatedMonoid_eq_closure]; exact AddSubmonoid.subset_closure ⟨i, rfl⟩⟩
  generates := (dilatedMonoid_eq_closure B D).symm
  positive i := Fin.cases B.q_positive
    (fun j => Nat.mul_pos (lt_trans B.q_positive hD) (weights_positive B j)) i
  minimal := dilated_minimal B D hD hcop
  pivot := 0

@[simp] theorem dilatedData_q (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) : (dilatedData B D hD hcop).q.val = B.q.val := rfl

@[simp] theorem dilatedData_weights (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) (j : Fin 3) :
    weights (dilatedData B D hD hcop) j = D * weights B j := by
  simp [weights, Data.tailDegrees, Data.degrees, Data.order, dilatedData, dilatedDegrees]

theorem dilatedData_isMultiplicity (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) : IsMultiplicity (dilatedData B D hD hcop) :=
  dilated_multiplicity B D hD

end NS25Lean.L2B
