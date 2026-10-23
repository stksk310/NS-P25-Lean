import NS25Lean.AppendixBNormalization
import NS25Lean.AppendixBZeroSum

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A
open ChosenBase L2C
variable {Gamma : NumericalSemigroup}

theorem pure_pair_forces_positive_representation (B : Data Gamma)
    (i j k l : Fin 4) (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (hkl : k ≠ l)
    (u v a b c d : ℕ) (hu : 0 < u) (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    (hi : weights B i = u * a) (hj : weights B j = u * b)
    (hk : weights B k = v * c) (hl : weights B l = v * d)
    (hfull : ∀ f : Fin 4 →₀ ℕ, weight B f = u * a * b ↔
      f = Finsupp.single i b ∨ f = Finsupp.single j a)
    (r : ℕ) (hr : r ∈ twoQuotient c d u) (hrpos : 0 < r) :
    ∃ R S : ℕ, 0 < R ∧ 0 < S ∧ v * r = a * R + b * S := by
  classical
  obtain ⟨K, L, hKL⟩ := (mem_twoGenerator c d (u * r)).mp hr
  have hex : ¬ twoGeneratorInt a b ((a : ℤ) * b - v * r) := by
    rintro ⟨R, S, he⟩
    have heN : a * R + b * S + v * r = a * b := by
      have heI : ((a * R + b * S + v * r : ℕ) : ℤ) = ((a * b : ℕ) : ℤ) := by
        push_cast
        linarith
      exact_mod_cast heI
    let f := Finsupp.single i R + Finsupp.single j S + Finsupp.single k K + Finsupp.single l L
    have hw : weight B f = u * a * b := by
      dsimp [f]
      simp only [map_add, weight_single, hi, hj, hk, hl]
      nlinarith [congrArg (fun z : ℕ => u * z) heN, congrArg (fun z : ℕ => v * z) hKL]
    have hK : K = 0 := by
      rcases (hfull f).mp hw with h | h
      · have := congrArg (fun z : Fin 4 →₀ ℕ => z k) h
        simpa [f, hki, hkj, hkl] using this
      · have := congrArg (fun z : Fin 4 →₀ ℕ => z k) h
        simpa [f, hki, hkj, hkl] using this
    have hL : L = 0 := by
      rcases (hfull f).mp hw with h | h
      · have := congrArg (fun z : Fin 4 →₀ ℕ => z l) h
        simpa [f, hli, hlj, hkl.symm] using this
      · have := congrArg (fun z : Fin 4 →₀ ℕ => z l) h
        simpa [f, hli, hlj, hkl.symm] using this
    rw [hK, hL] at hKL
    nlinarith
  obtain ⟨R, S, he⟩ := (two_generator_symmetry a b ha hb hc _).mp hex
  refine ⟨R + 1, S + 1, by omega, by omega, ?_⟩
  have heI : ((v * r : ℕ) : ℤ) = ((a * (R + 1) + b * (S + 1) : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast heI

namespace NormalizedPairs

def leftQuotient (N : NormalizedPairs B) : AddSubmonoid ℕ := twoQuotient N.alpha N.beta N.v
def rightQuotient (N : NormalizedPairs B) : AddSubmonoid ℕ := twoQuotient N.gamma N.delta N.u

theorem left_positive_of_right (N : NormalizedPairs B) (r : ℕ)
    (hr : r ∈ N.rightQuotient) (hp : 0 < r) :
    ∃ R S : ℕ, 0 < R ∧ 0 < S ∧ N.v * r = N.alpha * R + N.beta * S := by
  exact pure_pair_forces_positive_representation B (N.perm 0) (N.perm 1) (N.perm 2) (N.perm 3)
    (N.perm.injective.ne (by decide)) (N.perm.injective.ne (by decide))
    (N.perm.injective.ne (by decide)) (N.perm.injective.ne (by decide))
    (N.perm.injective.ne (by decide)) N.u N.v N.alpha N.beta N.gamma N.delta
    N.u_pos (by have := N.alpha_ge; omega) (by have := N.beta_ge; omega)
    N.ab_coprime N.weight0 N.weight1 N.weight2 N.weight3 N.pair0 r hr hp

theorem right_positive_of_left (N : NormalizedPairs B) (r : ℕ)
    (hr : r ∈ N.leftQuotient) (hp : 0 < r) :
    ∃ R S : ℕ, 0 < R ∧ 0 < S ∧ N.u * r = N.gamma * R + N.delta * S := by
  exact pure_pair_forces_positive_representation B (N.perm 2) (N.perm 3) (N.perm 0) (N.perm 1)
    (N.perm.injective.ne (by decide)) (N.perm.injective.ne (by decide))
    (N.perm.injective.ne (by decide)) (N.perm.injective.ne (by decide))
    (N.perm.injective.ne (by decide)) N.v N.u N.gamma N.delta N.alpha N.beta
    N.v_pos (by have := N.gamma_ge; omega) (by have := N.delta_ge; omega)
    N.cd_coprime N.weight2 N.weight3 N.weight0 N.weight1 N.pair1 r hr hp

theorem common_quotient (N : NormalizedPairs B) : N.leftQuotient = N.rightQuotient := by
  ext r
  by_cases hz : r = 0
  · subst r; simp
  have hp : 0 < r := by omega
  constructor
  · intro hr
    obtain ⟨R, S, _, _, he⟩ := N.right_positive_of_left r hr hp
    exact (mem_twoGenerator _ _ _).mpr ⟨R, S, he⟩
  · intro hr
    obtain ⟨R, S, _, _, he⟩ := N.left_positive_of_right r hr hp
    exact (mem_twoGenerator _ _ _).mpr ⟨R, S, he⟩

/-- The actual common quotient semigroup in Appendix B. -/
def T (N : NormalizedPairs B) : AddSubmonoid ℕ := N.leftQuotient

theorem positive_representations (N : NormalizedPairs B) (r : ℕ)
    (hr : r ∈ N.T) (hp : 0 < r) :
    (∃ R S : ℕ, 0 < R ∧ 0 < S ∧ N.v * r = N.alpha * R + N.beta * S) ∧
    (∃ K L : ℕ, 0 < K ∧ 0 < L ∧ N.u * r = N.gamma * K + N.delta * L) := by
  exact ⟨N.left_positive_of_right r (N.common_quotient ▸ hr) hp,
    N.right_positive_of_left r hr hp⟩

def a (N : NormalizedPairs B) : ℕ := reducedGenerator N.alpha N.v
def b (N : NormalizedPairs B) : ℕ := reducedGenerator N.beta N.v
def w (N : NormalizedPairs B) : ℕ := reducedScale N.alpha N.beta N.v

theorem reduced_T (N : NormalizedPairs B) : N.T = twoQuotient N.a N.b N.w :=
  reduced_quotient_eq N.alpha N.beta N.v (by have := N.alpha_ge; omega)
    (by have := N.beta_ge; omega) N.ab_coprime

theorem reduced_positive (N : NormalizedPairs B) (r : ℕ) (hr : r ∈ N.T) (hp : 0 < r) :
    ∃ R S : ℕ, 0 < R ∧ 0 < S ∧ N.w * r = N.a * R + N.b * S :=
  reduced_positive_representation N.alpha N.beta N.v r
    (by have := N.alpha_ge; omega) (by have := N.beta_ge; omega) N.ab_coprime
    (N.positive_representations r hr hp).1

theorem reduced_scale_gt (N : NormalizedPairs B) : max N.a N.b < N.w := by
  apply quotient_scale_gt N.a N.b N.w
  · exact reduced_generator_positive _ _ (by have := N.alpha_ge; omega)
  · exact reduced_generator_positive _ _ (by have := N.beta_ge; omega)
  · exact reduced_generators_coprime _ _ _ N.ab_coprime
  · intro r hr hp
    exact N.reduced_positive r (N.reduced_T.symm ▸ hr) hp

theorem zero_sum_lt (N : NormalizedPairs B) (hab : N.a < N.b) :
    N.b ∉ minimalPositiveGenerators N.T := by
  rw [N.reduced_T]
  exact zero_sum_exclusion_lt N.a N.b N.w
    (reduced_generator_positive _ _ (by have := N.alpha_ge; omega)) hab
    (lt_of_le_of_lt (le_max_left _ _) N.reduced_scale_gt)

theorem zero_sum_gt (N : NormalizedPairs B) (hba : N.b < N.a) :
    N.a ∉ minimalPositiveGenerators N.T := by
  rw [N.reduced_T]
  exact zero_sum_exclusion_gt N.a N.b N.w
    (reduced_generator_positive _ _ (by have := N.beta_ge; omega)) hba
    (lt_of_le_of_lt (le_max_right _ _) N.reduced_scale_gt)

end NormalizedPairs
end NS25Lean.L4A
