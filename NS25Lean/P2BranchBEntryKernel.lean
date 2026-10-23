import NS25Lean.P2NonsymmetricHerzogCompletion
import NS25Lean.P2SectorB

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open ChosenBase L2B L5A1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

abbrev rawA (R : SectorBCriticalRoleBranchB P) : ℕ :=
  weights P.M.base (R.reindex 0)

abbrev rawB (R : SectorBCriticalRoleBranchB P) : ℕ :=
  weights P.M.base (R.reindex 1)

abbrev rawC (R : SectorBCriticalRoleBranchB P) : ℕ :=
  weights P.M.base (R.reindex 2)

abbrev normalizedA (R : SectorBCriticalRoleBranchB P) : ℕ :=
  L5A2B4AR3.normalizedWeight P.M.base (R.reindex 0)

abbrev normalizedB (R : SectorBCriticalRoleBranchB P) : ℕ :=
  L5A2B4AR3.normalizedWeight P.M.base (R.reindex 1)

abbrev normalizedC (R : SectorBCriticalRoleBranchB P) : ℕ :=
  L5A2B4AR3.normalizedWeight P.M.base (R.reindex 2)

abbrev pH (R : SectorBCriticalRoleBranchB P) : ℕ := L5A2B4AR4R2B.r12 R
abbrev qH (R : SectorBCriticalRoleBranchB P) : ℕ := L5A2B4AR4R2B.r13 R
abbrev uH (R : SectorBCriticalRoleBranchB P) : ℕ := L5A2B4AR4R2B.r21 R
abbrev vH (R : SectorBCriticalRoleBranchB P) : ℕ := L5A2B4AR4R2B.r23 R
abbrev wH (R : SectorBCriticalRoleBranchB P) : ℕ := L5A2B4AR4R2B.r31 R
abbrev zH (R : SectorBCriticalRoleBranchB P) : ℕ := L5A2B4AR4R2B.r32 R

structure ActualHerzogCoordinates (R : SectorBCriticalRoleBranchB P) : Prop where
  cross_positive :
    0 < pH R ∧ 0 < qH R ∧ 0 < uH R ∧ 0 < vH R ∧ 0 < wH R ∧ 0 < zH R
  coefficient_sums :
    L5A2B4AR4R2B.c1 R = uH R + wH R ∧
      L5A2B4AR4R2B.c2 R = pH R + zH R ∧
      L5A2B4AR4R2B.c3 R = qH R + vH R
  raw_relations :
    L5A2B4AR4R2B.c1 R * rawA R = pH R * rawB R + qH R * rawC R ∧
      L5A2B4AR4R2B.c2 R * rawB R = uH R * rawA R + vH R * rawC R ∧
      L5A2B4AR4R2B.c3 R * rawC R = wH R * rawA R + zH R * rawB R
  normalized_relations :
    L5A2B4AR4R2B.c1 R * normalizedA R =
        pH R * normalizedB R + qH R * normalizedC R ∧
      L5A2B4AR4R2B.c2 R * normalizedB R =
        uH R * normalizedA R + vH R * normalizedC R ∧
      L5A2B4AR4R2B.c3 R * normalizedC R =
        wH R * normalizedA R + zH R * normalizedB R

theorem branchB_actual_herzog_coordinates (R : SectorBCriticalRoleBranchB P) :
    ActualHerzogCoordinates R := by
  let d := FourGeneratedBridge.tailGcd
    (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val
      (P.M.base.tailDegrees 2).val
  have hd : 0 < d := FourGeneratedBridge.tailGcd_pos (P.M.base.degrees_positive 1)
  have hs (i : Fin 3) :
      d * L5A2B4AR3.normalizedWeight P.M.base i = weights P.M.base i :=
    L5A2B4AR3.normalizedWeight_scale P.M.base i
  have hsA : d * normalizedA R = rawA R := hs (R.reindex 0)
  have hsB : d * normalizedB R = rawB R := hs (R.reindex 1)
  have hsC : d * normalizedC R = rawC R := hs (R.reindex 2)
  let C := L5A2B4AR4R2B.branchB_nonsymmetric_herzog_completion R
  refine {
    cross_positive := C.cross_positive
    coefficient_sums := C.coefficient_sums
    raw_relations := C.weighted_relations
    normalized_relations := ?_
  }
  obtain ⟨h1, h2, h3⟩ := C.weighted_relations
  constructor
  · apply Nat.eq_of_mul_eq_mul_left hd
    calc
      d * (L5A2B4AR4R2B.c1 R * normalizedA R) =
          L5A2B4AR4R2B.c1 R * rawA R := by nlinarith only [hsA]
      _ = pH R * rawB R + qH R * rawC R := h1
      _ = d * (pH R * normalizedB R + qH R * normalizedC R) := by
        nlinarith only [hsB, hsC]
  constructor
  · apply Nat.eq_of_mul_eq_mul_left hd
    calc
      d * (L5A2B4AR4R2B.c2 R * normalizedB R) =
          L5A2B4AR4R2B.c2 R * rawB R := by nlinarith only [hsB]
      _ = uH R * rawA R + vH R * rawC R := h2
      _ = d * (uH R * normalizedA R + vH R * normalizedC R) := by
        nlinarith only [hsA, hsC]
  · apply Nat.eq_of_mul_eq_mul_left hd
    calc
      d * (L5A2B4AR4R2B.c3 R * normalizedC R) =
          L5A2B4AR4R2B.c3 R * rawC R := by nlinarith only [hsC]
      _ = wH R * rawA R + zH R * rawB R := h3
      _ = d * (wH R * normalizedA R + zH R * normalizedB R) := by
        nlinarith only [hsA, hsB]

private theorem outside_zero_of_relation (R : SectorBCriticalRoleBranchB P)
    {q x y : ℕ} (hq : 0 < q)
    (h : q * rawA R = x * rawB R + y * rawC R) :
    OutsideExponent P.M.base (R.reindex 0) q := by
  refine ⟨hq, Finsupp.single (R.reindex 1) x + Finsupp.single (R.reindex 2) y, ?_, ?_⟩
  · simp
  · simpa [map_add, weight_single] using h.symm

private theorem outside_one_of_relation (R : SectorBCriticalRoleBranchB P)
    {q x y : ℕ} (hq : 0 < q)
    (h : q * rawB R = x * rawA R + y * rawC R) :
    OutsideExponent P.M.base (R.reindex 1) q := by
  refine ⟨hq, Finsupp.single (R.reindex 0) x + Finsupp.single (R.reindex 2) y, ?_, ?_⟩
  · simp
  · simpa [map_add, weight_single] using h.symm

private theorem outside_two_of_relation (R : SectorBCriticalRoleBranchB P)
    {q x y : ℕ} (hq : 0 < q)
    (h : q * rawC R = x * rawA R + y * rawB R) :
    OutsideExponent P.M.base (R.reindex 2) q := by
  refine ⟨hq, Finsupp.single (R.reindex 0) x + Finsupp.single (R.reindex 1) y, ?_, ?_⟩
  · simp
  · simpa [map_add, weight_single] using h.symm

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
    L5A2B.UniqueZeroInLShape (a : ℤ) (b : ℤ) (c : ℤ)
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
  have hni : ni < p + z := by
    rw [← hii] at hi
    exact_mod_cast hi
  have hnj : nj < q + v := by
    rw [← hjj] at hj
    exact_mod_cast hj
  have hncorner : ni < p ∨ nj < q := by
    rcases hcorner with h | h
    · rw [← hii] at h
      exact Or.inl (by exact_mod_cast h)
    · rw [← hjj] at h
      exact Or.inr (by exact_mod_cast h)
  have hnzero : ni * b + nj * c = nk * a := by
    rw [← hii, ← hjj, ← hkk] at hk
    exact_mod_cast hk
  obtain ⟨hni0, hnj0⟩ := unique_zero_nat a b c c1 c2 c3 p q v z
    ha hb hc hp hq hv hz hs2 hs3 hrel1 hmin1 hmin2 hmin3 hni hnj hncorner hnzero
  constructor
  · rw [← hii]
    exact_mod_cast hni0
  · rw [← hjj]
    exact_mod_cast hnj0

theorem branchB_actual_uniqueZeroInLShape (R : SectorBCriticalRoleBranchB P) :
    L5A2B.UniqueZeroInLShape
      (rawA R : ℤ) (rawB R : ℤ) (rawC R : ℤ)
      (pH R : ℤ) (qH R : ℤ) (zH R : ℤ) (vH R : ℤ) := by
  let C := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := C.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := C.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := C.raw_relations
  apply uniqueZeroInLShape_of_nat (rawA R) (rawB R) (rawC R)
    (L5A2B4AR4R2B.c1 R) (L5A2B4AR4R2B.c2 R) (L5A2B4AR4R2B.c3 R)
    (pH R) (qH R) (vH R) (zH R)
  · exact weights_positive P.M.base (R.reindex 0)
  · exact weights_positive P.M.base (R.reindex 1)
  · exact weights_positive P.M.base (R.reindex 2)
  · exact hp
  · exact hq
  · exact hv
  · exact hz
  · exact hs2
  · exact hs3
  · exact hrel1
  · intro n x y hn hrel
    exact criticalExponent_min P.M.base (R.reindex 0) n
      (outside_zero_of_relation R hn hrel)
  · intro n x y hn hrel
    exact criticalExponent_min P.M.base (R.reindex 1) n
      (outside_one_of_relation R hn hrel)
  · intro n x y hn hrel
    rw [← L5A2B4AR4R2B.branchB_third_criticalExponent R]
    exact criticalExponent_min P.M.base (R.reindex 2) n
      (outside_two_of_relation R hn hrel)

private theorem normalized_relation_to_raw (_R : SectorBCriticalRoleBranchB P)
    {n x y : ℕ} {i j k : Fin 3}
    (h : n * L5A2B4AR3.normalizedWeight P.M.base i =
      x * L5A2B4AR3.normalizedWeight P.M.base j +
        y * L5A2B4AR3.normalizedWeight P.M.base k) :
    n * weights P.M.base i = x * weights P.M.base j + y * weights P.M.base k := by
  let d := FourGeneratedBridge.tailGcd
    (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val
      (P.M.base.tailDegrees 2).val
  have hi := L5A2B4AR3.normalizedWeight_scale P.M.base i
  have hj := L5A2B4AR3.normalizedWeight_scale P.M.base j
  have hk := L5A2B4AR3.normalizedWeight_scale P.M.base k
  change d * L5A2B4AR3.normalizedWeight P.M.base i = weights P.M.base i at hi
  change d * L5A2B4AR3.normalizedWeight P.M.base j = weights P.M.base j at hj
  change d * L5A2B4AR3.normalizedWeight P.M.base k = weights P.M.base k at hk
  nlinarith only [h, hi, hj, hk]

/-- Critical minimality for a positive relation with normalized `a` on the
left.  This is the public Branch-B-local wrapper used by the family-local
M2/M3 classification. -/
theorem branchB_normalizedA_relation_min
    (R : SectorBCriticalRoleBranchB P) (q x y : ℕ) (hq : 0 < q)
    (hrel : q * normalizedA R = x * normalizedB R + y * normalizedC R) :
    L5A2B4AR4R2B.c1 R ≤ q := by
  exact criticalExponent_min P.M.base (R.reindex 0) q
    (outside_zero_of_relation R hq
      (normalized_relation_to_raw R (i := R.reindex 0) (j := R.reindex 1)
        (k := R.reindex 2) hrel))

/-- Critical minimality for a positive relation with normalized `b` on the
left. -/
theorem branchB_normalizedB_relation_min
    (R : SectorBCriticalRoleBranchB P) (q x y : ℕ) (hq : 0 < q)
    (hrel : q * normalizedB R = x * normalizedA R + y * normalizedC R) :
    L5A2B4AR4R2B.c2 R ≤ q := by
  exact criticalExponent_min P.M.base (R.reindex 1) q
    (outside_one_of_relation R hq
      (normalized_relation_to_raw R (i := R.reindex 1) (j := R.reindex 0)
        (k := R.reindex 2) hrel))

/-- Critical minimality for a positive relation with normalized `c` on the
left.  The third critical exponent is the actual Branch-B theorem, not an
extra field or premise. -/
theorem branchB_normalizedC_relation_min
    (R : SectorBCriticalRoleBranchB P) (q x y : ℕ) (hq : 0 < q)
    (hrel : q * normalizedC R = x * normalizedA R + y * normalizedB R) :
    L5A2B4AR4R2B.c3 R ≤ q := by
  rw [← L5A2B4AR4R2B.branchB_third_criticalExponent R]
  exact criticalExponent_min P.M.base (R.reindex 2) q
    (outside_two_of_relation R hq
      (normalized_relation_to_raw R (i := R.reindex 2) (j := R.reindex 0)
        (k := R.reindex 1) hrel))

theorem branchB_actual_normalized_uniqueZeroInLShape
    (R : SectorBCriticalRoleBranchB P) :
    L5A2B.UniqueZeroInLShape
      (normalizedA R : ℤ) (normalizedB R : ℤ) (normalizedC R : ℤ)
      (pH R : ℤ) (qH R : ℤ) (zH R : ℤ) (vH R : ℤ) := by
  let C := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := C.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := C.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := C.normalized_relations
  let d := FourGeneratedBridge.tailGcd
    (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val
      (P.M.base.tailDegrees 2).val
  have hscale (i : Fin 3) :
      d * L5A2B4AR3.normalizedWeight P.M.base i = weights P.M.base i :=
    L5A2B4AR3.normalizedWeight_scale P.M.base i
  have hA : 0 < normalizedA R := by
    by_contra hn
    have hzA : normalizedA R = 0 := Nat.eq_zero_of_not_pos hn
    have hsA := hscale (R.reindex 0)
    change d * normalizedA R = rawA R at hsA
    rw [hzA, mul_zero] at hsA
    exact (weights_positive P.M.base (R.reindex 0)).ne' hsA.symm
  have hB : 0 < normalizedB R := by
    by_contra hn
    have hzB : normalizedB R = 0 := Nat.eq_zero_of_not_pos hn
    have hsB := hscale (R.reindex 1)
    change d * normalizedB R = rawB R at hsB
    rw [hzB, mul_zero] at hsB
    exact (weights_positive P.M.base (R.reindex 1)).ne' hsB.symm
  have hC : 0 < normalizedC R := by
    by_contra hn
    have hzC : normalizedC R = 0 := Nat.eq_zero_of_not_pos hn
    have hsC := hscale (R.reindex 2)
    change d * normalizedC R = rawC R at hsC
    rw [hzC, mul_zero] at hsC
    exact (weights_positive P.M.base (R.reindex 2)).ne' hsC.symm
  apply uniqueZeroInLShape_of_nat (normalizedA R) (normalizedB R) (normalizedC R)
    (L5A2B4AR4R2B.c1 R) (L5A2B4AR4R2B.c2 R) (L5A2B4AR4R2B.c3 R)
    (pH R) (qH R) (vH R) (zH R) hA hB hC hp hq hv hz hs2 hs3 hrel1
  · intro n x y hn hrel
    exact criticalExponent_min P.M.base (R.reindex 0) n
      (outside_zero_of_relation R hn
        (normalized_relation_to_raw R (i := R.reindex 0) (j := R.reindex 1)
          (k := R.reindex 2) hrel))
  · intro n x y hn hrel
    exact criticalExponent_min P.M.base (R.reindex 1) n
      (outside_one_of_relation R hn
        (normalized_relation_to_raw R (i := R.reindex 1) (j := R.reindex 0)
          (k := R.reindex 2) hrel))
  · intro n x y hn hrel
    rw [← L5A2B4AR4R2B.branchB_third_criticalExponent R]
    exact criticalExponent_min P.M.base (R.reindex 2) n
      (outside_two_of_relation R hn
        (normalized_relation_to_raw R (i := R.reindex 2) (j := R.reindex 0)
          (k := R.reindex 1) hrel))

theorem branchB_actual_inverse_boundary_first
    (R : SectorBCriticalRoleBranchB P) (I J : ℤ)
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (harm :
      (∃ s tau : ℤ,
        1 ≤ s ∧ s < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
          L5A2B.RepresentsZero (normalizedA R) (normalizedB R) (normalizedC R)
            (pH R + s + I) (tau + J)) ∨
      (∃ s tau : ℤ,
        1 ≤ s ∧ s < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
          L5A2B.RepresentsZero (normalizedA R) (normalizedB R) (normalizedC R)
            (s + I) (qH R + tau + J))) :
    1 ≤ I ∨ (qH R : ℤ) ≤ J := by
  let C := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := C.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := C.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := C.normalized_relations
  have hpZ : (0 : ℤ) < pH R := by exact_mod_cast hp
  have hqZ : (0 : ℤ) < qH R := by exact_mod_cast hq
  have hzZ : (0 : ℤ) < zH R := by exact_mod_cast hz
  have hvZ : (0 : ℤ) < vH R := by exact_mod_cast hv
  have hrel1Z :
      (pH R : ℤ) * normalizedB R + qH R * normalizedC R =
        L5A2B4AR4R2B.c1 R * normalizedA R := by
    exact_mod_cast hrel1.symm
  have hrel3Z :
      ((qH R : ℕ) + vH R : ℤ) * normalizedC R =
        wH R * normalizedA R + zH R * normalizedB R := by
    have hrel3Nat :
        (qH R + vH R) * normalizedC R =
          wH R * normalizedA R + zH R * normalizedB R := by
      rw [← hs3]
      exact hrel3
    exact_mod_cast hrel3Nat
  exact L5A2B.inverse_boundary_first
    (normalizedA R) (normalizedB R) (normalizedC R)
    (L5A2B4AR4R2B.c1 R) (wH R) (pH R) (qH R) (zH R) (vH R)
    I J hpZ hqZ hzZ hvZ hI hJ hrel1Z hrel3Z
    (branchB_actual_normalized_uniqueZeroInLShape R) harm

theorem branchB_actual_inverse_boundary_second
    (R : SectorBCriticalRoleBranchB P) (I J : ℤ)
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (harm :
      (∃ s tau : ℤ,
        1 ≤ s ∧ s < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
          L5A2B.RepresentsZero (normalizedA R) (normalizedB R) (normalizedC R)
            (pH R + s + I) (tau + J)) ∨
      (∃ s tau : ℤ,
        1 ≤ s ∧ s < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
          L5A2B.RepresentsZero (normalizedA R) (normalizedB R) (normalizedC R)
            (s + I) (qH R + tau + J))) :
    1 ≤ J ∨ (pH R : ℤ) ≤ I := by
  let C := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := C.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := C.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := C.normalized_relations
  have hpZ : (0 : ℤ) < pH R := by exact_mod_cast hp
  have hqZ : (0 : ℤ) < qH R := by exact_mod_cast hq
  have hzZ : (0 : ℤ) < zH R := by exact_mod_cast hz
  have hvZ : (0 : ℤ) < vH R := by exact_mod_cast hv
  have hrel1Z :
      (pH R : ℤ) * normalizedB R + qH R * normalizedC R =
        L5A2B4AR4R2B.c1 R * normalizedA R := by
    exact_mod_cast hrel1.symm
  have hrel2Z :
      ((pH R : ℕ) + zH R : ℤ) * normalizedB R =
        uH R * normalizedA R + vH R * normalizedC R := by
    have hrel2Nat :
        (pH R + zH R) * normalizedB R =
          uH R * normalizedA R + vH R * normalizedC R := by
      rw [← hs2]
      exact hrel2
    exact_mod_cast hrel2Nat
  exact L5A2B.inverse_boundary_second
    (normalizedA R) (normalizedB R) (normalizedC R)
    (L5A2B4AR4R2B.c1 R) (uH R) (pH R) (qH R) (zH R) (vH R)
    I J hpZ hqZ hzZ hvZ hI hJ hrel1Z hrel2Z
    (branchB_actual_normalized_uniqueZeroInLShape R) harm

private theorem exists_reindexed_normalized_factorization
    (R : SectorBCriticalRoleBranchB P) {n : ℕ}
    (hn : n ∈ L5A2B4AR1.normalizedH P.M.base) :
    ∃ x y z : ℕ,
      n = x * normalizedA R + y * normalizedB R + z * normalizedC R := by
  let B := P.M.base
  have hgen := (L5A2B4AR1.normalized_minimalThree B).1
  have hnGen : n ∈ FourGeneratedBridge.generatedThree
      (L5A2B4AR1.normalizedA B) (L5A2B4AR1.normalizedB B)
        (L5A2B4AR1.normalizedC B) := by
    change n ∈ NumericalSemigroup.generatedBy
      {L5A2B4AR1.normalizedA B, L5A2B4AR1.normalizedB B,
        L5A2B4AR1.normalizedC B}
    rw [← hgen]
    exact hn
  obtain ⟨x0, x1, x2, hnEq⟩ :=
    (FourGeneratedBridge.mem_generatedThree_iff _ _ _ _).mp hnGen
  let v : Fin 3 →₀ ℕ :=
    Finsupp.single 0 x0 + Finsupp.single 1 x1 + Finsupp.single 2 x2
  have hsum : n = ∑ i : Fin 3,
      v i * L5A2B4AR3.normalizedWeight B i := by
    rw [hnEq]
    simp [v, Fin.sum_univ_succ, L5A2B4AR3.normalizedWeight,
      L2B.weights, ChosenBase.Data.tailDegrees, L5A2B4AR1.normalizedA,
      L5A2B4AR1.normalizedB, L5A2B4AR1.normalizedC, Nat.add_assoc]
  refine ⟨v (R.reindex 0), v (R.reindex 1), v (R.reindex 2), ?_⟩
  calc
    n = ∑ i : Fin 3, v i * L5A2B4AR3.normalizedWeight B i := hsum
    _ = ∑ i : Fin 3,
        v (R.reindex i) * L5A2B4AR3.normalizedWeight B (R.reindex i) := by
          rw [← Equiv.sum_comp R.reindex]
    _ = v (R.reindex 0) * normalizedA R +
        v (R.reindex 1) * normalizedB R +
          v (R.reindex 2) * normalizedC R := by
      simp [Fin.sum_univ_succ, normalizedA, normalizedB, normalizedC, B,
        Nat.add_assoc]

structure ActualPrefixSourceCoordinates
    (R : SectorBCriticalRoleBranchB P) (s : ℤ) where
  ell : ℕ
  return_witness :
    L5A2B4AR1.ReturnWitness (L5A2B4AR1.normalizedH P.M.base)
      (L5A2B4AR1.normalizedM P.M.base) (L5A2B4AR1.actualPrincipalIndex P.M.base)
      s ell
  sourceValue : ℕ
  returnedValue : ℕ
  source_mem : sourceValue ∈ L5A2B4AR1.normalizedH P.M.base
  returned_mem : returnedValue ∈ L5A2B4AR1.normalizedH P.M.base
  source_eq : (sourceValue : ℤ) = s
  returned_eq :
    (returnedValue : ℤ) = s - (ell * L5A2B4AR1.normalizedM P.M.base : ℕ)
  sourceX : ℕ
  sourceY : ℕ
  sourceZ : ℕ
  returnedX : ℕ
  returnedY : ℕ
  returnedZ : ℕ
  source_factorization :
    sourceValue = sourceX * normalizedA R + sourceY * normalizedB R +
      sourceZ * normalizedC R
  returned_factorization :
    returnedValue = returnedX * normalizedA R + returnedY * normalizedB R +
      returnedZ * normalizedC R

noncomputable def branchB_actual_prefix_source_coordinates
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : L5A2B4AR1.IsBranchBirth (L5A2B4AR1.normalizedH P.M.base)
      (L5A2B4AR1.normalizedM P.M.base) (L5A2B4AR1.actualPrincipalIndex P.M.base) s) :
    ActualPrefixSourceCoordinates R s := by
  let ell := L5A2B4AR1.sectorBCanonicalReturnIndex P hB hs
  have hreturn := L5A2B4AR1.sectorBCanonicalReturnIndex_spec P hB hs
  have hsJ := hreturn.2.2.1
  let hsource := (NumericalSemigroup.mem_asRelativeIdeal_iff
    (L5A2B4AR1.normalizedH P.M.base) s).1 hsJ.1
  let sourceValue := hsource.choose
  have hsourceSpec := hsource.choose_spec
  let hreturned := (NumericalSemigroup.mem_asRelativeIdeal_iff
    (L5A2B4AR1.normalizedH P.M.base)
      (s - (ell * L5A2B4AR1.normalizedM P.M.base : ℕ))).1 hsJ.2
  let returnedValue := hreturned.choose
  have hreturnedSpec := hreturned.choose_spec
  let hsourceCoordinates :=
    exists_reindexed_normalized_factorization R hsourceSpec.1
  let sourceX := hsourceCoordinates.choose
  let sourceY := hsourceCoordinates.choose_spec.choose
  let sourceZ := hsourceCoordinates.choose_spec.choose_spec.choose
  have hsourceFactorization :=
    hsourceCoordinates.choose_spec.choose_spec.choose_spec
  let hreturnedCoordinates :=
    exists_reindexed_normalized_factorization R hreturnedSpec.1
  let returnedX := hreturnedCoordinates.choose
  let returnedY := hreturnedCoordinates.choose_spec.choose
  let returnedZ := hreturnedCoordinates.choose_spec.choose_spec.choose
  have hreturnedFactorization :=
    hreturnedCoordinates.choose_spec.choose_spec.choose_spec
  exact {
    ell := ell
    return_witness := hreturn
    sourceValue := sourceValue
    returnedValue := returnedValue
    source_mem := hsourceSpec.1
    returned_mem := hreturnedSpec.1
    source_eq := hsourceSpec.2.symm
    returned_eq := hreturnedSpec.2.symm
    sourceX := sourceX
    sourceY := sourceY
    sourceZ := sourceZ
    returnedX := returnedX
    returnedY := returnedY
    returnedZ := returnedZ
    source_factorization := hsourceFactorization
    returned_factorization := hreturnedFactorization
  }

/-- The first unproved coordinate target after the source-exact kernel:
every integer residue modulo the first normalized weight has one L-shape
representative.  This is a target definition, not an added hypothesis. -/
def ActualLShapeCoordinatesComplete (R : SectorBCriticalRoleBranchB P) : Prop :=
  ∀ n : ℤ, ∃! ij : ℤ × ℤ,
    L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) ij.1 ij.2 ∧
      Int.ModEq (normalizedA R)
        (ij.1 * normalizedB R + ij.2 * normalizedC R) n

end NS25Lean.L5A2B4AR5B
