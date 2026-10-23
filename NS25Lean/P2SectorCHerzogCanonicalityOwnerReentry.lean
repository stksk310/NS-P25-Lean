import NS25Lean.P2SectorCGridPhysicalOffsetDictionary
import NS25Lean.P2SectorCCoherentKappaStencil
import NS25Lean.P2SectorB

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR5

open ChosenBase FourGeneratedBridge
open L2B L5A2B L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR3 L5A2C4OR4

variable {Gamma : NumericalSemigroup}

/-- The paper Herzog L-shape, stated only with the actual coherent
coefficients and their actual critical-exponent sums. -/
def HerzogLShapeDomain {B : Data Gamma} {e : Fin 3 ≃ Fin 3}
    (D : CoherentHerzogData B e) (i j : ℕ) : Prop :=
  i < c2 B e ∧ j < c3 B e ∧ (i < cr12 D ∨ j < cr13 D)

private theorem routing_scale_zero (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B e * routingA B e = weights B (e 0) := by
  simpa [normalizedGrid, gridDegree] using normalizedGrid_scale B e 1 0 0

private theorem routing_scale_one (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B e * routingB B e = weights B (e 1) := by
  simpa [normalizedGrid, gridDegree] using normalizedGrid_scale B e 0 1 0

private theorem routing_scale_two (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B e * routingC B e = weights B (e 2) := by
  simpa [normalizedGrid, gridDegree] using normalizedGrid_scale B e 0 0 1

/-- The three coherent relations descend to the actual gcd-normalized routing
weights; no normalized relation is stored in `CoherentHerzogData`. -/
theorem coherent_normalized_relations (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    c1 B e * routingA B e = cr12 D * routingB B e + cr13 D * routingC B e ∧
      c2 B e * routingB B e = cr21 D * routingA B e + cr23 D * routingC B e ∧
      c3 B e * routingC B e = cr31 D * routingA B e + cr32 D * routingB B e := by
  have hd : 0 < routingD B e :=
    tailGcd_pos (weights_positive B (e 0))
  have hs0 := routing_scale_zero B e
  have hs1 := routing_scale_one B e
  have hs2 := routing_scale_two B e
  obtain ⟨h1, h2, h3⟩ := coherent_relations B e D
  constructor
  · apply Nat.eq_of_mul_eq_mul_left hd
    nlinarith only [hs0, hs1, hs2, h1]
  constructor
  · apply Nat.eq_of_mul_eq_mul_left hd
    nlinarith only [hs0, hs1, hs2, h2]
  · apply Nat.eq_of_mul_eq_mul_left hd
    nlinarith only [hs0, hs1, hs2, h3]

private theorem outside_zero_of_normalized_relation (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3) {q x y : ℕ} (hq : 0 < q)
    (h : q * routingA B e = x * routingB B e + y * routingC B e) :
    OutsideExponent B (e 0) q := by
  refine ⟨hq, Finsupp.single (e 1) x + Finsupp.single (e 2) y, ?_, ?_⟩
  · simp
  · have hs0 := routing_scale_zero B e
    have hs1 := routing_scale_one B e
    have hs2 := routing_scale_two B e
    have hr : q * weights B (e 0) =
        x * weights B (e 1) + y * weights B (e 2) := by
      nlinarith only [h, hs0, hs1, hs2]
    simpa [map_add, weight_single] using hr.symm

private theorem outside_one_of_normalized_relation (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3) {q x y : ℕ} (hq : 0 < q)
    (h : q * routingB B e = x * routingA B e + y * routingC B e) :
    OutsideExponent B (e 1) q := by
  refine ⟨hq, Finsupp.single (e 0) x + Finsupp.single (e 2) y, ?_, ?_⟩
  · simp
  · have hs0 := routing_scale_zero B e
    have hs1 := routing_scale_one B e
    have hs2 := routing_scale_two B e
    have hr : q * weights B (e 1) =
        x * weights B (e 0) + y * weights B (e 2) := by
      nlinarith only [h, hs0, hs1, hs2]
    simpa [map_add, weight_single] using hr.symm

private theorem outside_two_of_normalized_relation (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3) {q x y : ℕ} (hq : 0 < q)
    (h : q * routingC B e = x * routingA B e + y * routingB B e) :
    OutsideExponent B (e 2) q := by
  refine ⟨hq, Finsupp.single (e 0) x + Finsupp.single (e 1) y, ?_, ?_⟩
  · simp
  · have hs0 := routing_scale_zero B e
    have hs1 := routing_scale_one B e
    have hs2 := routing_scale_two B e
    have hr : q * weights B (e 2) =
        x * weights B (e 0) + y * weights B (e 1) := by
      nlinarith only [h, hs0, hs1, hs2]
    simpa [map_add, weight_single] using hr.symm

private theorem unique_zero_nat
    (a b c c1 c2 c3 p q v z : ℕ)
    (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hp : 0 < p) (hq : 0 < q) (_hv : 0 < v) (_hz : 0 < z)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hrel1 : c1 * a = p * b + q * c)
    (hmin1 : ∀ n x y : ℕ, 0 < n → n * a = x * b + y * c → c1 ≤ n)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n)
    {i j k : ℕ} (hi : i < p + z) (hj : j < q + v)
    (hcorner : i < p ∨ j < q) (hzero : i * b + j * c = k * a) :
    i = 0 ∧ j = 0 := by
  by_cases hk0 : k = 0
  · subst k
    constructor <;> nlinarith
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hc1k : c1 ≤ k := hmin1 k i j hk hzero.symm
  rcases hcorner with hip | hjq
  · have hqj : q < j := by
      by_contra hn
      have hjle : j ≤ q := by omega
      nlinarith only [hzero, hrel1, hip, hjle, hb, hc, hc1k, _ha]
    have hsubk : k - c1 + c1 = k := Nat.sub_add_cancel hc1k
    have hsubi : p - i + i = p := Nat.sub_add_cancel (le_of_lt hip)
    have hsubj : j - q + q = j := Nat.sub_add_cancel (le_of_lt hqj)
    have hrel : (j - q) * c = (k - c1) * a + (p - i) * b := by
      nlinarith only [hzero, hrel1, hsubk, hsubi, hsubj]
    have hmin := hmin3 (j - q) (k - c1) (p - i) (Nat.sub_pos_of_lt hqj) hrel
    omega
  · have hpi : p < i := by
      by_contra hn
      have hile : i ≤ p := by omega
      nlinarith only [hzero, hrel1, hjq, hile, hb, hc, hc1k, _ha]
    have hsubk : k - c1 + c1 = k := Nat.sub_add_cancel hc1k
    have hsubi : i - p + p = i := Nat.sub_add_cancel (le_of_lt hpi)
    have hsubj : q - j + j = q := Nat.sub_add_cancel (le_of_lt hjq)
    have hrel : (i - p) * b = (k - c1) * a + (q - j) * c := by
      nlinarith only [hzero, hrel1, hsubk, hsubi, hsubj]
    have hmin := hmin2 (i - p) (k - c1) (q - j) (Nat.sub_pos_of_lt hpi) hrel
    omega

private theorem uniqueZeroInLShape_of_nat
    (a b c c1 c2 c3 p q v z : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hp : 0 < p) (hq : 0 < q) (hv : 0 < v) (hz : 0 < z)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hrel1 : c1 * a = p * b + q * c)
    (hmin1 : ∀ n x y : ℕ, 0 < n → n * a = x * b + y * c → c1 ≤ n)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n) :
    UniqueZeroInLShape (a : ℤ) (b : ℤ) (c : ℤ)
      (p : ℤ) (q : ℤ) (z : ℤ) (v : ℤ) := by
  intro i j hshape hzero
  rcases hshape with ⟨hi0, hj0, hi, hj, hcorner⟩
  rcases hzero with ⟨k, hk⟩
  have hk0 : 0 ≤ k := by nlinarith
  let ni := i.toNat
  let nj := j.toNat
  let nk := k.toNat
  have hii : (ni : ℤ) = i := Int.toNat_of_nonneg hi0
  have hjj : (nj : ℤ) = j := Int.toNat_of_nonneg hj0
  have hkk : (nk : ℤ) = k := Int.toNat_of_nonneg hk0
  have hni : ni < p + z := by rw [← hii] at hi; exact_mod_cast hi
  have hnj : nj < q + v := by rw [← hjj] at hj; exact_mod_cast hj
  have hncorner : ni < p ∨ nj < q := by
    rcases hcorner with h | h
    · rw [← hii] at h; exact Or.inl (by exact_mod_cast h)
    · rw [← hjj] at h; exact Or.inr (by exact_mod_cast h)
  have hnzero : ni * b + nj * c = nk * a := by
    rw [← hii, ← hjj, ← hkk] at hk
    exact_mod_cast hk
  obtain ⟨hni0, hnj0⟩ := unique_zero_nat a b c c1 c2 c3 p q v z
    ha hb hc hp hq hv hz hs2 hs3 hrel1 hmin1 hmin2 hmin3 hni hnj hncorner hnzero
  constructor
  · rw [← hii]; exact_mod_cast hni0
  · rw [← hjj]; exact_mod_cast hnj0

/-- The source-exact zero-residue rigidity of the coherent Sector-C L-shape.
This is strictly weaker than completeness/canonicality of every point. -/
theorem coherent_uniqueZeroInLShape (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    UniqueZeroInLShape
      (routingA B e : ℤ) (routingB B e : ℤ) (routingC B e : ℤ)
      (cr12 D : ℤ) (cr13 D : ℤ) (cr32 D : ℤ) (cr23 D : ℤ) := by
  have hp := coherent_coefficients_positive B e D
  have hs := coherent_coefficients B e D
  have hr := coherent_normalized_relations B e D
  have hbpos : 0 < routingB B e :=
    quotient_pos_of_dvd (weights_positive B (e 1))
      (tailGcd_dvd (routingN1 B e) (routingN2 B e) (routingN3 B e)).2.1
  have hcpos : 0 < routingC B e :=
    quotient_pos_of_dvd (weights_positive B (e 2))
      (tailGcd_dvd (routingN1 B e) (routingN2 B e) (routingN3 B e)).2.2
  apply uniqueZeroInLShape_of_nat (routingA B e) (routingB B e) (routingC B e)
    (c1 B e) (c2 B e) (c3 B e) (cr12 D) (cr13 D) (cr23 D) (cr32 D)
  · exact routingA_pos B e
  · exact hbpos
  · exact hcpos
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.2.1
  · exact hp.2.2.2.2.2
  · exact hs.2.1
  · exact hs.2.2
  · exact hr.1
  · intro n x y hn hrel
    exact criticalExponent_min B (e 0) n
      (outside_zero_of_normalized_relation B e hn hrel)
  · intro n x y hn hrel
    exact criticalExponent_min B (e 1) n
      (outside_one_of_normalized_relation B e hn hrel)
  · intro n x y hn hrel
    exact criticalExponent_min B (e 2) n
      (outside_two_of_normalized_relation B e hn hrel)

/-- All seven paper load-bearing coordinates lie in the actual coherent
Herzog L-shape.  This theorem makes no Apéry/canonicality assertion. -/
theorem loadBearingCoordinates_in_domain (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    HerzogLShapeDomain D 0 0 ∧
      HerzogLShapeDomain D (cr12 D - 1) (cr13 D) ∧
      HerzogLShapeDomain D (cr12 D) (cr13 D - 1) ∧
      HerzogLShapeDomain D 0 (c3 B e - 1) ∧
      HerzogLShapeDomain D (cr32 D) 0 ∧
      HerzogLShapeDomain D (cr32 D - 1) 0 ∧
      HerzogLShapeDomain D (coherentKappa1 B e D).1
        (coherentKappa1 B e D).2 := by
  have hp := coherent_coefficients_positive B e D
  have hb := coherent_strict_bounds B e D
  have hc := coherent_coefficients B e D
  simp only [HerzogLShapeDomain, coherentKappa1]
  omega

/-- Exact statement of the first still-open load-bearing theorem.  It is a
target proposition, not a field, premise, axiom, or claimed proof. -/
def HerzogLShapeCanonicality (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : Prop :=
  ∀ i j, HerzogLShapeDomain D i j → IsCanonicalTailGridPoint B e i j

/-- The origin is independently canonical; this does not use or assume the
open whole-domain canonicality target. -/
theorem H0_isCanonicalTailGridPoint (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    IsCanonicalTailGridPoint B e 0 0 := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  rw [isCanonicalTailGridPoint_iff_tailGridLift_eq_zero]
  have hs := tailGridLift_spec B e 0 0
  have hm := (routingH B e).asRelativeIdeal.aperyRepresentative_mem
    (routingA B e) (0 : ZMod (routingA B e))
  change physicalAlpha B e (0 : ZMod (routingA B e)) ∈
    (routingH B e).asRelativeIdeal at hm
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hm
  obtain ⟨n, -, hn⟩ := hm
  have hs' : (0 : ℤ) = physicalAlpha B e (0 : ZMod (routingA B e)) +
      routingA B e * tailGridLift B e 0 0 := by
    simpa [normalizedGrid, gridResidue] using hs
  rw [hn] at hs'
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hl0 : (0 : ℤ) ≤ tailGridLift B e 0 0 := by
    exact_mod_cast Nat.zero_le (tailGridLift B e 0 0)
  nlinarith [hs']

end NS25Lean.L5A2C4OR5


