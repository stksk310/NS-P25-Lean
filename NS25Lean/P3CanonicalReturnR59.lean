import NS25Lean.P3StrictReturnFormsR58
import NS25Lean.P3ReturnNormalizationR59

set_option linter.style.header false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.P3R59
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4A L5A2C4D L5A2C4H L5A2B4AR1
open L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

def RBReturn (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) : Prop :=
  ∃ s t d : ℕ, 0 < s ∧ s < P3R57.roleCoefficient M hp e 2 1 ∧
    0 < t ∧ t < P3R57.roleCoefficient M hp e 0 2 ∧
    0 < d ∧ d < P3R57.roleCoefficient M hp e 1 0 ∧
    ((P3R57.roleCoefficient M hp e 0 1 + s : ℕ) : ℤ) * routingB M.base e +
      t * routingC M.base e = q * M.base.q.val + d * routingA M.base e

def LTReturn (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) : Prop :=
  ∃ s t d : ℕ, 0 < s ∧ s < P3R57.roleCoefficient M hp e 0 1 ∧
    0 < t ∧ t < P3R57.roleCoefficient M hp e 1 2 ∧
    0 < d ∧ d < P3R57.roleCoefficient M hp e 2 0 ∧
    (s : ℤ) * routingB M.base e +
      ((P3R57.roleCoefficient M hp e 0 2 + t : ℕ) : ℤ) * routingC M.base e =
        q * M.base.q.val + d * routingA M.base e

def OneArmPrefix (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) : Prop :=
  (∀ q : ℕ, 0 < q → q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
    RBReturn M hp e q) ∨
  (∀ q : ℕ, 0 < q → q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
    LTReturn M hp e q)

/-- Frozen coherent completeness instantiated with actual P3 witnesses. -/
theorem apery_lshape_coordinate (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (n : ℕ) :
    ∃ i j : ℕ, i < criticalExponent M.base (e 1) ∧
      j < criticalExponent M.base (e 2) ∧
      (i < P3R57.roleCoefficient M hp e 0 1 ∨
        j < P3R57.roleCoefficient M hp e 0 2) ∧
      IsCanonicalTailGridPoint M.base e i j ∧
      Int.ModEq (routingA M.base e) (normalizedGrid M.base e 0 i j) n := by
  let HD := P3R58.p3_coherentHerzogData M hp e
  obtain ⟨ij, ⟨hL, hmod⟩, _⟩ := coherent_lShape_unique_coordinate M.base e HD n
  rcases hL with ⟨hi0, hj0, hi, hj, hcorner⟩
  have hsi : (ij.1.toNat : ℤ) = ij.1 := Int.toNat_of_nonneg hi0
  have hsj : (ij.2.toNat : ℤ) = ij.2 := Int.toNat_of_nonneg hj0
  have hs := coherent_coefficients M.base e HD
  have hid : ij.1.toNat < criticalExponent M.base (e 1) := by
    have hi' : (ij.1.toNat : ℤ) < c2 M.base e := by
      rw [hsi, hs.2.1]
      exact_mod_cast hi
    exact_mod_cast hi'
  have hjd : ij.2.toNat < criticalExponent M.base (e 2) := by
    have hj' : (ij.2.toNat : ℤ) < c3 M.base e := by
      rw [hsj, hs.2.2]
      exact_mod_cast hj
    exact_mod_cast hj'
  have hcd : ij.1.toNat < P3R57.roleCoefficient M hp e 0 1 ∨
      ij.2.toNat < P3R57.roleCoefficient M hp e 0 2 := by
    change ij.1.toNat < cr12 HD ∨ ij.2.toNat < cr13 HD
    rcases hcorner with hc | hc
    · exact Or.inl (by exact_mod_cast (hsi ▸ hc))
    · exact Or.inr (by exact_mod_cast (hsj ▸ hc))
  exact ⟨_, _, hid, hjd, hcd,
    P3R58.p3_lshape_canonical M hp e _ _ hid hjd hcd,
    by simpa [normalizedGrid, hsi, hsj] using hmod⟩

/-- Actual normalized canonical representative lies strictly above a nonprincipal level. -/
theorem normalized_nonprincipal_canonical_return (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    ∃ i j d : ℕ, i < criticalExponent M.base (e 1) ∧
      j < criticalExponent M.base (e 2) ∧
      (i < P3R57.roleCoefficient M hp e 0 1 ∨
        j < P3R57.roleCoefficient M hp e 0 2) ∧
      IsCanonicalTailGridPoint M.base e i j ∧ 0 < d ∧
      (i : ℤ) * routingB M.base e + j * routingC M.base e =
        q * M.base.q.val + d * routingA M.base e := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  obtain ⟨i, j, hi, hj, hc, hcan, hmod⟩ := apery_lshape_coordinate M hp e (q * M.base.q.val)
  let beta := normalizedGrid M.base e 0 i j
  have hnot : q * M.base.q.val ∉ routingH M.base e := by
    intro hm
    exact (Nat.not_le_of_gt hpre) (principalIndex_min _ _ _ hq hm)
  have ha : routingA M.base e ∈ routingH M.base e := by
    change _ ∈ generatedThree _ _ _
    exact AddSubmonoid.subset_closure (by simp)
  have hb : beta ∈ routingH M.base e := by
    change normalizedGrid M.base e 0 i j ∈ generatedThree _ _ _
    exact (mem_generatedThree_iff _ _ _ _).mpr ⟨0, i, j, by simp [normalizedGrid]⟩
  have hcast : (beta : ZMod (routingA M.base e)) =
      ((q * M.base.q.val : ℕ) : ZMod (routingA M.base e)) := by
    exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).2 hmod
  have hlt : q * M.base.q.val < beta := by
    by_contra hn
    obtain ⟨k, hk⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
      (routingA M.base e) (w := (beta : ℤ)) (z := (q * M.base.q.val : ℕ)) (by exact_mod_cast (show beta ≤ q * M.base.q.val by omega)) (by exact_mod_cast hcast.symm)
    have heq : q * M.base.q.val = beta + routingA M.base e * k := by exact_mod_cast hk
    apply hnot
    rw [heq]
    exact (routingH M.base e).toAddSubmonoid.add_mem hb
      (by simpa [nsmul_eq_mul, Nat.mul_comm] using
        (routingH M.base e).toAddSubmonoid.nsmul_mem ha k)
  obtain ⟨d, hd⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
    (routingA M.base e) (w := (q * M.base.q.val : ℕ)) (z := (beta : ℤ)) (by exact_mod_cast hlt.le) (by exact_mod_cast hcast)
  have hdpos : 0 < d := by
    by_contra hn
    have hz : d = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero, add_zero] at hd
    have := (show (q * M.base.q.val : ℤ) < beta by exact_mod_cast hlt)
    omega
  refine ⟨i, j, d, hi, hj, hc, hcan, hdpos, ?_⟩
  simpa [beta, normalizedGrid, Nat.cast_add, Nat.cast_mul, mul_comm] using hd




/-- Every positive nonprincipal normalized level has a strict RB or LT return,
using the actual live first critical axis and the original multiplier D*q. -/
theorem canonical_nonprincipal_return (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0) * weights M.base (e 0) - weights M.base k ∈ M.base.apery) :
    ∀ q : ℕ, 0 < q →
      q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
      RBReturn M hp e q ∨ LTReturn M hp e q := by
  intro q hq hpre
  obtain ⟨i, j, d, hi, hj, hc, hcan, hd, he⟩ :=
    normalized_nonprincipal_canonical_return M hp e q hq hpre
  have hn : q * M.base.q.val ∉ routingH M.base e := by
    intro hm
    exact (Nat.not_le_of_gt hpre) (principalIndex_min _ _ _ hq hm)
  have hnon := normalized_nonprincipal_original M.base e q hn
  have hell : 0 < routingD M.base e * q := Nat.mul_pos (routingD_positive M.base e) hq
  have heN : i * routingB M.base e + j * routingC M.base e =
      q * M.base.q.val + d * routingA M.base e := by exact_mod_cast he
  have hs := P3R58.routing_scale_weights M.base e
  have heOrig : i * weights M.base (e 1) + j * weights M.base (e 2) =
      (routingD M.base e * q) * M.base.q.val + d * weights M.base (e 0) := by
    calc
      _ = routingD M.base e * (i * routingB M.base e + j * routingC M.base e) := by
        rw [← hs.2.1, ← hs.2.2]; ring
      _ = routingD M.base e * (q * M.base.q.val + d * routingA M.base e) := by rw [heN]
      _ = _ := by rw [← hs.1]; ring
  obtain ⟨_, hform⟩ := P3R58.nonprincipal_strict_return_form M hp e
    (routingD M.base e * q) i j d hell hnon hi hj hc hlive heOrig
  have hsum := P3R58.p3_coefficient_sums M hp e
  rcases hform with ⟨hpi, hj0, hjq, hdu⟩ | ⟨hi0, hip, hqj, hdw⟩
  · left
    have hiEq : P3R57.roleCoefficient M hp e 0 1 +
        (i - P3R57.roleCoefficient M hp e 0 1) = i := by omega
    refine ⟨i - P3R57.roleCoefficient M hp e 0 1, j, d,
      by omega, by omega, hj0, hjq, hd, hdu, ?_⟩
    rw [hiEq]
    exact he
  · right
    have hjEq : P3R57.roleCoefficient M hp e 0 2 +
        (j - P3R57.roleCoefficient M hp e 0 2) = j := by omega
    refine ⟨i, j - P3R57.roleCoefficient M hp e 0 2, d,
      hi0, hip, by omega, by omega, hd, hdw, ?_⟩
    rw [hjEq]
    exact he





/-- Every actual normalized tail Apéry state is represented by a canonical L-cell. -/
theorem apery_lshape_surjective (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA M.base e)) :
    ∃ i j : ℕ, i < criticalExponent M.base (e 1) ∧
      j < criticalExponent M.base (e 2) ∧
      (i < P3R57.roleCoefficient M hp e 0 1 ∨
        j < P3R57.roleCoefficient M hp e 0 2) ∧
      IsCanonicalTailGridPoint M.base e i j ∧
      physicalAlpha M.base e s =
        (i : ℤ) * routingB M.base e + j * routingC M.base e := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  obtain ⟨i, j, hi, hj, hc, hcan, hmod⟩ := apery_lshape_coordinate M hp e s.val
  have hm : ((normalizedGrid M.base e 0 i j : ℕ) : ZMod (routingA M.base e)) = s := by
    have hm' := (ZMod.intCast_eq_intCast_iff _ _ _).2 hmod
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hm'
  have hr : gridResidue M.base e i j = s :=
    (normalizedGrid_mod M.base e 0 i j).symm.trans hm
  refine ⟨i, j, hi, hj, hc, hcan, ?_⟩
  rw [← hr, ← hcan]
  simp only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul]

end NS25Lean.P3R59
