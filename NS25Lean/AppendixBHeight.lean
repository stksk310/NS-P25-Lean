import NS25Lean.AppendixBPresentation
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A
open ChosenBase L2C Presentation
variable {Gamma : NumericalSemigroup}

theorem factorizationMap_four {H : Type*} [AddCommMonoid H] (w : Fin 4 → H)
    (f : Fin 4 →₀ ℕ) : factorizationMap w f = f 0 • w 0 + f 1 • w 1 + f 2 • w 2 + f 3 • w 3 := by
  have hf : f = Finsupp.single 0 (f 0) + Finsupp.single 1 (f 1) +
      Finsupp.single 2 (f 2) + Finsupp.single 3 (f 3) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hf]
  simp only [map_add, factorizationMap_single]

theorem factorizationMap_weights (B : Data Gamma) (f : Fin 4 →₀ ℕ) :
    factorizationMap (weights B) f = weight B f := by
  rw [factorizationMap_four, weight_eq_sum, Fin.sum_univ_four]
  simp

theorem factorKernel_mono (K : Type*) [Field K] {H H' : Type*}
    [AddCommMonoid H] [AddCommMonoid H'] (w : Fin 4 → H) (w' : Fin 4 → H')
    (h : ∀ x y, factorizationMap w x = factorizationMap w y →
      factorizationMap w' x = factorizationMap w' y) :
    RingHom.ker (factorizationAlgebraMap K w).toRingHom ≤
      RingHom.ker (factorizationAlgebraMap K w').toRingHom := by
  rw [← relationIdeal_factorization_eq_ker, ← relationIdeal_factorization_eq_ker]
  apply Ideal.span_mono
  apply Set.image_mono
  rintro ⟨x, y⟩ hxy
  exact h x y hxy

theorem relationBinomial_mem_factorKernel (K : Type*) [Field K] {H : Type*} [AddCommMonoid H]
    (w : Fin 4 → H) (x y : Fin 4 →₀ ℕ) :
    relationBinomial K (x, y) ∈ RingHom.ker (factorizationAlgebraMap K w).toRingHom ↔
      factorizationMap w x = factorizationMap w y := by
  rw [← relationIdeal_factorization_eq_ker, relationBinomial_mem_iff,
    generatedCongruence_all_relations]
  rfl

def heightWeights1 (n : Fin 4 → ℕ) : Fin 4 → (Fin 4 →₀ ℕ) :=
  ![Finsupp.single 0 (n 0), Finsupp.single 0 (n 1), Finsupp.single 2 1, Finsupp.single 3 1]

def heightWeights2 (n : Fin 4 → ℕ) : Fin 4 → (Fin 4 →₀ ℕ) :=
  ![Finsupp.single 0 (n 0), Finsupp.single 0 (n 1), Finsupp.single 0 (n 2), Finsupp.single 3 1]

theorem heightWeights1_value (n : Fin 4 → ℕ) (f : Fin 4 →₀ ℕ) :
    factorizationMap (heightWeights1 n) f =
      Finsupp.single 0 (f 0 * n 0 + f 1 * n 1) + Finsupp.single 2 (f 2) + Finsupp.single 3 (f 3) := by
  rw [factorizationMap_four]
  simp [heightWeights1, Finsupp.smul_single, Finsupp.single_add]

theorem heightWeights2_value (n : Fin 4 → ℕ) (f : Fin 4 →₀ ℕ) :
    factorizationMap (heightWeights2 n) f =
      Finsupp.single 0 (f 0 * n 0 + f 1 * n 1 + f 2 * n 2) + Finsupp.single 3 (f 3) := by
  rw [factorizationMap_four]
  simp [heightWeights2, Finsupp.smul_single, Finsupp.single_add]

/-- A strict chain of three prime kernels certifies actual toric codimension at least three. -/
theorem toric_height_ge_three (K : Type*) [Field K] (B : Data Gamma) :
    3 ≤ (ToricPresentation.toricIdeal K Gamma.toAddSubmonoid B.family).height := by
  classical
  let n := weights B
  let P1 := RingHom.ker (factorizationAlgebraMap K (heightWeights1 n)).toRingHom
  let P2 := RingHom.ker (factorizationAlgebraMap K (heightWeights2 n)).toRingHom
  let P3 := RingHom.ker (factorizationAlgebraMap K n).toRingHom
  haveI : P1.IsPrime := RingHom.ker_isPrime _
  haveI : P2.IsPrime := RingHom.ker_isPrime _
  haveI : P3.IsPrime := RingHom.ker_isPrime _
  have h12 : P1 ≤ P2 := by
    apply factorKernel_mono
    intro x y he
    rw [heightWeights1_value, heightWeights1_value] at he
    have h0 := congrArg (fun f : Fin 4 →₀ ℕ => f 0) he
    have h2 := congrArg (fun f : Fin 4 →₀ ℕ => f 2) he
    have h3 := congrArg (fun f : Fin 4 →₀ ℕ => f 3) he
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2),
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 3)] at h0
    have h2' : x 2 = y 2 := by simpa using h2
    have h3' : x 3 = y 3 := by simpa using h3
    rw [heightWeights2_value, heightWeights2_value, h2', h3']
    congr 2
    omega
  have h23 : P2 ≤ P3 := by
    apply factorKernel_mono
    intro x y he
    rw [heightWeights2_value, heightWeights2_value] at he
    have h0 := congrArg (fun f : Fin 4 →₀ ℕ => f 0) he
    have h3 := congrArg (fun f : Fin 4 →₀ ℕ => f 3) he
    have h0' : x 0 * n 0 + x 1 * n 1 + x 2 * n 2 =
        y 0 * n 0 + y 1 * n 1 + y 2 * n 2 := by simpa using h0
    have h3' : x 3 = y 3 := by simpa using h3
    simp only [factorizationMap_four, nsmul_eq_mul, Nat.cast_id, h3', h0']
  have hn : ∀ i, 0 < n i := weights_positive B
  have h01 : (⊥ : Ideal (MvPolynomial (Fin 4) K)) < P1 := by
    apply lt_of_le_of_ne bot_le
    intro he
    let f : MvPolynomial (Fin 4) K := relationBinomial K (Finsupp.single 0 (n 1), Finsupp.single 1 (n 0))
    have hm : f ∈ P1 := by
      apply (relationBinomial_mem_factorKernel K _ _ _).mpr
      simp [factorizationMap_single, heightWeights1, Finsupp.smul_single, mul_comm]
    have hz : f = 0 := by simpa [← he] using hm
    have hv : (Finsupp.single 0 (n 1) : Fin 4 →₀ ℕ) = Finsupp.single 1 (n 0) :=
      AddMonoidAlgebra.single_left_injective (one_ne_zero : (1 : K) ≠ 0) (sub_eq_zero.mp hz)
    have hc := congrArg (fun z : Fin 4 →₀ ℕ => z 0) hv
    simp at hc
    have := hn 1
    omega
  have h12s : P1 < P2 := by
    apply lt_of_le_of_ne h12
    intro he
    have hm : relationBinomial K (Finsupp.single 0 (n 2), Finsupp.single 2 (n 0)) ∈ P2 := by
      apply (relationBinomial_mem_factorKernel K _ _ _).mpr
      simp [factorizationMap_single, heightWeights2, Finsupp.smul_single, mul_comm]
    rw [← he] at hm
    have hv := (relationBinomial_mem_factorKernel K _ _ _).mp hm
    have hc := congrArg (fun z : Fin 4 →₀ ℕ => z 2) hv
    simp [factorizationMap_single, heightWeights1, Finsupp.smul_single] at hc
    have := hn 0
    omega
  have h23s : P2 < P3 := by
    apply lt_of_le_of_ne h23
    intro he
    have hm : relationBinomial K (Finsupp.single 0 (n 3), Finsupp.single 3 (n 0)) ∈ P3 := by
      apply (relationBinomial_mem_factorKernel K _ _ _).mpr
      simp [factorizationMap_single, nsmul_eq_mul, mul_comm]
    rw [← he] at hm
    have hv := (relationBinomial_mem_factorKernel K _ _ _).mp hm
    have hc := congrArg (fun z : Fin 4 →₀ ℕ => z 3) hv
    simp [factorizationMap_single, heightWeights2, Finsupp.smul_single] at hc
    have := hn 0
    omega
  have hP3 : P3 = ToricPresentation.toricIdeal K Gamma.toAddSubmonoid B.family := by
    change P3 = RingHom.ker (ToricPresentation.toricMap K _ _).toRingHom
    rw [← factorizationAlgebraMap_eq_toricMap]
    apply le_antisymm
    · apply factorKernel_mono
      intro x y he
      apply Subtype.ext
      rw [← weight_eq_degree, ← weight_eq_degree]
      simpa [n, factorizationMap_weights] using he
    · apply factorKernel_mono
      intro x y he
      rw [factorizationMap_weights, factorizationMap_weights]
      rw [weight_eq_degree, weight_eq_degree]
      exact congrArg Subtype.val he
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h01
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime h12s
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime h23s
  rw [← hP3]
  calc
    (3 : ℕ∞) ≤ ((⊥ : Ideal (MvPolynomial (Fin 4) K)).height + 1) + 1 + 1 := by
      norm_num [Ideal.height_bot]
    _ ≤ (P1.height + 1) + 1 := add_le_add (add_le_add h1 le_rfl) le_rfl
    _ ≤ P2.height + 1 := add_le_add h2 le_rfl
    _ ≤ P3.height := h3

end NS25Lean.L4A
