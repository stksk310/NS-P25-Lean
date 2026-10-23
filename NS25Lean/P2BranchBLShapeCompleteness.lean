import NS25Lean.P2BranchBEntryKernel

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open ChosenBase L2B L5A1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- A disjoint finite indexing of the Herzog L-shape: the full left arm and
the lower part of the right arm. -/
abbrev LShapeIndex (p q z v : ℕ) :=
  (Fin p × Fin (q + v)) ⊕ (Fin z × Fin q)

def lShapePair (p q z v : ℕ) : LShapeIndex p q z v → ℤ × ℤ
  | Sum.inl ij => (ij.1.val, ij.2.val)
  | Sum.inr sj => (p + sj.1.val, sj.2.val)

def lShapeResidue (a b c p q z v : ℕ) (x : LShapeIndex p q z v) : ZMod a :=
  ((lShapePair p q z v x).1 * b + (lShapePair p q z v x).2 * c : ℤ)

private theorem lShapePair_mem
    {p q z v : ℕ} (x : LShapeIndex p q z v) :
    L5A2B.InLShape p q z v
      (lShapePair p q z v x).1 (lShapePair p q z v x).2 := by
  rcases x with ij | sj
  · rcases ij with ⟨i, j⟩
    unfold L5A2B.InLShape
    simp only [lShapePair]
    constructor
    · exact_mod_cast i.val.zero_le
    constructor
    · exact_mod_cast j.val.zero_le
    constructor
    · exact_mod_cast lt_of_lt_of_le i.isLt (Nat.le_add_right p z)
    constructor
    · exact_mod_cast j.isLt
    · left
      exact_mod_cast i.isLt
  · rcases sj with ⟨s, j⟩
    simp only [lShapePair]
    unfold L5A2B.InLShape
    norm_num
    omega

private theorem exists_lShapeIndex_of_mem
    {p q z v : ℕ} {i j : ℤ}
    (h : L5A2B.InLShape p q z v i j) :
    ∃ x : LShapeIndex p q z v,
      lShapePair p q z v x = (i, j) := by
  rcases h with ⟨hi0, hj0, hibound, hjbound, hcorner⟩
  by_cases hip : i < (p : ℤ)
  · let ii : Fin p := ⟨i.toNat, by
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 hip⟩
    let jj : Fin (q + v) := ⟨j.toNat, by
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 hjbound⟩
    refine ⟨Sum.inl (ii, jj), ?_⟩
    simp [lShapePair, ii, jj, Int.toNat_of_nonneg hi0, Int.toNat_of_nonneg hj0]
  · have hpi : (p : ℤ) ≤ i := le_of_not_gt hip
    have hjq : j < (q : ℤ) := hcorner.resolve_left hip
    have hisub0 : 0 ≤ i - (p : ℤ) := by omega
    have hisubz : i - (p : ℤ) < (z : ℤ) := by omega
    let ss : Fin z := ⟨(i - (p : ℤ)).toNat, by
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 hisubz⟩
    let jj : Fin q := ⟨j.toNat, by
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 hjq⟩
    refine ⟨Sum.inr (ss, jj), ?_⟩
    simp [lShapePair, ss, jj,
      Int.toNat_of_nonneg hisub0, Int.toNat_of_nonneg hj0]
    omega

private theorem lshape_cross_impossible
    (a b c c2 c3 p q z v : ℕ)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n)
    {i j i' j' : ℤ}
    (hmod : Int.ModEq a (i * b + j * c) (i' * b + j' * c))
    (hiStrict : i' < i) (hjStrict : j < j')
    (hi'Nonneg : 0 ≤ i') (hjNonneg : 0 ≤ j)
    (hiBound : i < (p + z : ℕ)) (hjBound : j' < (q + v : ℕ)) : False := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  let I := (i - i').toNat
  let J := (j' - j).toNat
  have hIZ : (I : ℤ) = i - i' := Int.toNat_of_nonneg (by omega)
  have hJZ : (J : ℤ) = j' - j := Int.toNat_of_nonneg (by omega)
  have hIpos : 0 < I := by omega
  have hJpos : 0 < J := by omega
  have hIlt : I < p + z := by omega
  have hJlt : J < q + v := by omega
  by_cases hk0 : 0 ≤ k
  · let K := k.toNat
    have hKZ : (K : ℤ) = k := Int.toNat_of_nonneg hk0
    have hrel : J * c = K * a + I * b := by
      exact_mod_cast (show (J : ℤ) * c = (K : ℤ) * a + (I : ℤ) * b by
        rw [hIZ, hJZ, hKZ]
        nlinarith)
    have := hmin3 J K I hJpos hrel
    omega
  · have hkneg : k < 0 := lt_of_not_ge hk0
    let K := (-k).toNat
    have hKZ : (K : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hrel : I * b = K * a + J * c := by
      exact_mod_cast (show (I : ℤ) * b = (K : ℤ) * a + (J : ℤ) * c by
        rw [hIZ, hJZ, hKZ]
        nlinarith)
    have := hmin2 I K J hIpos hrel
    omega

private theorem lshape_modEq_unique
    (a b c c2 c3 p q z v : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hz : 0 < z) (hv : 0 < v)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n)
    (hunique : L5A2B.UniqueZeroInLShape a b c p q z v)
    {i j i' j' : ℤ}
    (hshape : L5A2B.InLShape p q z v i j)
    (hshape' : L5A2B.InLShape p q z v i' j')
    (hmod : Int.ModEq a (i * b + j * c) (i' * b + j' * c)) :
    i = i' ∧ j = j' := by
  rcases hshape with ⟨hi0, hj0, hi, hj, hcorner⟩
  rcases hshape' with ⟨hi0', hj0', hi', hj', hcorner'⟩
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hmod)
  by_cases hii : i' ≤ i
  · by_cases hjj : j' ≤ j
    · have hdshape : L5A2B.InLShape p q z v (i - i') (j - j') := by
        unfold L5A2B.InLShape
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        · rcases hcorner with hip | hjq
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
      have hzero : L5A2B.RepresentsZero a b c (i - i') (j - j') := by
        refine ⟨-k, ?_⟩
        nlinarith
      obtain ⟨hieq, hjeq⟩ := hunique _ _ hdshape hzero
      omega
    · have hjcross : j < j' := lt_of_not_ge hjj
      have hiStrict : i' < i := by
        by_contra hn
        have hieq : i = i' := by omega
        subst i'
        have hdshape : L5A2B.InLShape p q z v 0 (j' - j) := by
          unfold L5A2B.InLShape
          constructor
          · omega
          constructor
          · omega
          constructor
          · omega
          constructor
          · omega
          · exact Or.inl (by omega)
        have hzero : L5A2B.RepresentsZero a b c 0 (j' - j) := by
          refine ⟨k, ?_⟩
          nlinarith
        have := hunique _ _ hdshape hzero
        omega
      exact False.elim (lshape_cross_impossible a b c c2 c3 p q z v hs2 hs3
        hmin2 hmin3 hmod hiStrict hjcross hi0' hj0 hi hj')
  · have hiCross : i < i' := lt_of_not_ge hii
    by_cases hjj : j ≤ j'
    · have hdshape : L5A2B.InLShape p q z v (i' - i) (j' - j) := by
        unfold L5A2B.InLShape
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        · rcases hcorner' with hip | hjq
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
      have hzero : L5A2B.RepresentsZero a b c (i' - i) (j' - j) := by
        refine ⟨k, ?_⟩
        nlinarith
      obtain ⟨hieq, hjeq⟩ := hunique _ _ hdshape hzero
      omega
    · have hjCross : j' < j := lt_of_not_ge hjj
      have hswap : Int.ModEq a (i' * b + j' * c) (i * b + j * c) := hmod.symm
      exact False.elim (lshape_cross_impossible a b c c2 c3 p q z v hs2 hs3
        hmin2 hmin3 hswap hiCross hjCross hi0 hj0' hi' hj)

private theorem gcd_eq_one_of_generatedByThree
    (H : NumericalSemigroup) (a b c : ℕ)
    (hfactor : ∀ x : ℕ, x ∈ H → ∃ u v w : ℕ, x = u * a + v * b + w * c) :
    Nat.gcd a (Nat.gcd b c) = 1 := by
  let g := Nat.gcd a (Nat.gcd b c)
  have hga : g ∣ a := Nat.gcd_dvd_left _ _
  have hgb : g ∣ b := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  have hgc : g ∣ c := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  have hall : ∀ x : ℕ, x ∈ H → g ∣ x := by
    intro x hx
    obtain ⟨u, v, w, rfl⟩ := hfactor x hx
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right hga u)
      (dvd_mul_of_dvd_right hgb v)) (dvd_mul_of_dvd_right hgc w)
  obtain ⟨N, hN⟩ := H.exists_conductor
  have hgN := hall N (hN N (le_refl N))
  have hgN1 := hall (N + 1) (hN (N + 1) (by omega))
  change g = 1
  apply Nat.eq_one_of_dvd_one
  have hone : Nat.Coprime N (N + 1) := by
    rw [Nat.coprime_self_add_right]
    simp
  rw [← hone.gcd_eq_one]
  exact Nat.dvd_gcd hgN hgN1

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
  let coeff : Fin 3 →₀ ℕ :=
    Finsupp.single 0 x0 + Finsupp.single 1 x1 + Finsupp.single 2 x2
  have hsum : n = ∑ i : Fin 3,
      coeff i * L5A2B4AR3.normalizedWeight B i := by
    rw [hnEq]
    simp [coeff, Fin.sum_univ_succ, L5A2B4AR3.normalizedWeight,
      L2B.weights, ChosenBase.Data.tailDegrees, L5A2B4AR1.normalizedA,
      L5A2B4AR1.normalizedB, L5A2B4AR1.normalizedC, Nat.add_assoc]
  refine ⟨coeff (R.reindex 0), coeff (R.reindex 1), coeff (R.reindex 2), ?_⟩
  calc
    n = ∑ i : Fin 3, coeff i * L5A2B4AR3.normalizedWeight B i := hsum
    _ = ∑ i : Fin 3,
        coeff (R.reindex i) * L5A2B4AR3.normalizedWeight B (R.reindex i) := by
          rw [← Equiv.sum_comp R.reindex]
    _ = coeff (R.reindex 0) * normalizedA R +
        coeff (R.reindex 1) * normalizedB R +
          coeff (R.reindex 2) * normalizedC R := by
      simp [Fin.sum_univ_succ, normalizedA, normalizedB, normalizedC, B,
        Nat.add_assoc]

/-- Public Branch-B interface to the reindexed normalized three-generator
factorization used by the L-shape completeness proof. -/
theorem branchB_exists_reindexed_normalized_factorization
    (R : SectorBCriticalRoleBranchB P) {n : ℕ}
    (hn : n ∈ L5A2B4AR1.normalizedH P.M.base) :
    ∃ x y z : ℕ,
      n = x * normalizedA R + y * normalizedB R + z * normalizedC R :=
  exists_reindexed_normalized_factorization R hn

private theorem normalized_relation_to_raw_lshape
    (R : SectorBCriticalRoleBranchB P)
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

private theorem outside_one_of_normalized_relation
    (R : SectorBCriticalRoleBranchB P) {n x y : ℕ} (hn : 0 < n)
    (h : n * normalizedB R = x * normalizedA R + y * normalizedC R) :
    OutsideExponent P.M.base (R.reindex 1) n := by
  refine ⟨hn, Finsupp.single (R.reindex 0) x + Finsupp.single (R.reindex 2) y, ?_, ?_⟩
  · simp
  · have hraw := normalized_relation_to_raw_lshape R
      (i := R.reindex 1) (j := R.reindex 0) (k := R.reindex 2) h
    simpa [map_add, weight_single] using hraw.symm

private theorem outside_two_of_normalized_relation
    (R : SectorBCriticalRoleBranchB P) {n x y : ℕ} (hn : 0 < n)
    (h : n * normalizedC R = x * normalizedA R + y * normalizedB R) :
    OutsideExponent P.M.base (R.reindex 2) n := by
  refine ⟨hn, Finsupp.single (R.reindex 0) x + Finsupp.single (R.reindex 1) y, ?_, ?_⟩
  · simp
  · have hraw := normalized_relation_to_raw_lshape R
      (i := R.reindex 2) (j := R.reindex 0) (k := R.reindex 1) h
    simpa [map_add, weight_single] using hraw.symm

private theorem lShapeResidue_injective (R : SectorBCriticalRoleBranchB P) :
    Function.Injective
      (lShapeResidue (normalizedA R) (normalizedB R) (normalizedC R)
        (pH R) (qH R) (zH R) (vH R)) := by
  let C := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := C.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := C.coefficient_sums
  intro x y hxy
  have hxshape := lShapePair_mem x
  have hyshape := lShapePair_mem y
  have hmod : Int.ModEq (normalizedA R)
      ((lShapePair (pH R) (qH R) (zH R) (vH R) x).1 * normalizedB R +
        (lShapePair (pH R) (qH R) (zH R) (vH R) x).2 * normalizedC R)
      ((lShapePair (pH R) (qH R) (zH R) (vH R) y).1 * normalizedB R +
        (lShapePair (pH R) (qH R) (zH R) (vH R) y).2 * normalizedC R) := by
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hxy
  have hcoords := lshape_modEq_unique
    (normalizedA R) (normalizedB R) (normalizedC R)
    (L5A2B4AR4R2B.c2 R) (L5A2B4AR4R2B.c3 R)
    (pH R) (qH R) (zH R) (vH R) hp hq hz hv hs2 hs3
    (fun n a c hn hrel =>
      criticalExponent_min P.M.base (R.reindex 1) n
        (outside_one_of_normalized_relation R hn hrel))
    (fun n a b hn hrel => by
      rw [← L5A2B4AR4R2B.branchB_third_criticalExponent R]
      exact criticalExponent_min P.M.base (R.reindex 2) n
        (outside_two_of_normalized_relation R hn hrel))
    (branchB_actual_normalized_uniqueZeroInLShape R)
    hxshape hyshape hmod
  rcases x with x | x <;> rcases y with y | y
  · rcases x with ⟨xi, xj⟩
    rcases y with ⟨yi, yj⟩
    simp only [lShapePair] at hcoords
    obtain ⟨hfirst, hsecond⟩ := hcoords
    cases Fin.ext (by omega : xi.val = yi.val)
    cases Fin.ext (by omega : xj.val = yj.val)
    rfl
  · rcases x with ⟨xi, xj⟩
    rcases y with ⟨ys, yj⟩
    simp only [lShapePair] at hcoords
    obtain ⟨hfirst, hsecond⟩ := hcoords
    exfalso
    have hylt : (ys.val : ℤ) < zH R := by exact_mod_cast ys.isLt
    have hxlt : (xi.val : ℤ) < pH R := by exact_mod_cast xi.isLt
    omega
  · rcases x with ⟨xs, xj⟩
    rcases y with ⟨yi, yj⟩
    simp only [lShapePair] at hcoords
    obtain ⟨hfirst, hsecond⟩ := hcoords
    exfalso
    have hxlt : (xs.val : ℤ) < zH R := by exact_mod_cast xs.isLt
    have hylt : (yi.val : ℤ) < pH R := by exact_mod_cast yi.isLt
    omega
  · rcases x with ⟨xs, xj⟩
    rcases y with ⟨ys, yj⟩
    simp only [lShapePair] at hcoords
    obtain ⟨hfirst, hsecond⟩ := hcoords
    cases Fin.ext (by omega : xs.val = ys.val)
    cases Fin.ext (by omega : xj.val = yj.val)
    rfl

private theorem normalizedA_dvd_lShapeCard
    (R : SectorBCriticalRoleBranchB P) :
    normalizedA R ∣ pH R * (qH R + vH R) + zH R * qH R := by
  let C := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := C.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := C.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := C.normalized_relations
  let D := pH R * (qH R + vH R) + zH R * qH R
  have hDb : D * normalizedB R =
      (qH R * uH R + vH R * L5A2B4AR4R2B.c1 R) * normalizedA R := by
    dsimp [D]
    calc
      (pH R * (qH R + vH R) + zH R * qH R) * normalizedB R =
          qH R * ((pH R + zH R) * normalizedB R) +
            vH R * (pH R * normalizedB R) := by ring
      _ = qH R * (uH R * normalizedA R + vH R * normalizedC R) +
            vH R * (pH R * normalizedB R) := by rw [← hs2, hrel2]
      _ = qH R * uH R * normalizedA R +
            vH R * (pH R * normalizedB R + qH R * normalizedC R) := by ring
      _ = qH R * uH R * normalizedA R +
            vH R * (L5A2B4AR4R2B.c1 R * normalizedA R) := by rw [← hrel1]
      _ = (qH R * uH R + vH R * L5A2B4AR4R2B.c1 R) * normalizedA R := by ring
  have hDc : D * normalizedC R =
      (pH R * wH R + zH R * L5A2B4AR4R2B.c1 R) * normalizedA R := by
    dsimp [D]
    calc
      (pH R * (qH R + vH R) + zH R * qH R) * normalizedC R =
          pH R * ((qH R + vH R) * normalizedC R) +
            zH R * (qH R * normalizedC R) := by ring
      _ = pH R * (wH R * normalizedA R + zH R * normalizedB R) +
            zH R * (qH R * normalizedC R) := by rw [← hs3, hrel3]
      _ = pH R * wH R * normalizedA R +
            zH R * (pH R * normalizedB R + qH R * normalizedC R) := by ring
      _ = pH R * wH R * normalizedA R +
            zH R * (L5A2B4AR4R2B.c1 R * normalizedA R) := by rw [← hrel1]
      _ = (pH R * wH R + zH R * L5A2B4AR4R2B.c1 R) * normalizedA R := by ring
  have hADb : normalizedA R ∣ D * normalizedB R := by
    rw [hDb]
    exact dvd_mul_left _ _
  have hADc : normalizedA R ∣ D * normalizedC R := by
    rw [hDc]
    exact dvd_mul_left _ _
  have hgcd := gcd_eq_one_of_generatedByThree
    (L5A2B4AR1.normalizedH P.M.base)
      (normalizedA R) (normalizedB R) (normalizedC R)
      (fun n hn => exists_reindexed_normalized_factorization R hn)
  have hcop : Nat.Coprime (normalizedA R) (Nat.gcd (normalizedB R) (normalizedC R)) := by
    exact hgcd
  have hAgcd : normalizedA R ∣ Nat.gcd (D * normalizedB R) (D * normalizedC R) :=
    Nat.dvd_gcd hADb hADc
  rw [Nat.gcd_mul_left] at hAgcd
  exact hcop.dvd_of_dvd_mul_right hAgcd

theorem branchB_actual_lShape_coordinates_complete
    (R : SectorBCriticalRoleBranchB P) :
    ActualLShapeCoordinatesComplete R := by
  let f := lShapeResidue (normalizedA R) (normalizedB R) (normalizedC R)
    (pH R) (qH R) (zH R) (vH R)
  have hinj : Function.Injective f := lShapeResidue_injective R
  have hcardIndex : Fintype.card (LShapeIndex (pH R) (qH R) (zH R) (vH R)) =
      pH R * (qH R + vH R) + zH R * qH R := by
    simp [LShapeIndex]
  have hapos : 0 < normalizedA R := by
    by_contra hn
    have ha0 : normalizedA R = 0 := Nat.eq_zero_of_not_pos hn
    have hscale := L5A2B4AR3.normalizedWeight_scale P.M.base (R.reindex 0)
    change FourGeneratedBridge.tailGcd _ _ _ * normalizedA R = rawA R at hscale
    rw [ha0, mul_zero] at hscale
    exact (weights_positive P.M.base (R.reindex 0)).ne' hscale.symm
  letI : NeZero (normalizedA R) := ⟨hapos.ne'⟩
  have hle : pH R * (qH R + vH R) + zH R * qH R ≤ normalizedA R := by
    rw [← hcardIndex, ← ZMod.card (normalizedA R)]
    exact Fintype.card_le_of_injective f hinj
  have hpos : 0 < pH R * (qH R + vH R) + zH R * qH R := by
    obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
      (branchB_actual_herzog_coordinates R).cross_positive
    positivity
  have hge : normalizedA R ≤ pH R * (qH R + vH R) + zH R * qH R :=
    Nat.le_of_dvd hpos (normalizedA_dvd_lShapeCard R)
  have hcard : Fintype.card (LShapeIndex (pH R) (qH R) (zH R) (vH R)) =
      Fintype.card (ZMod (normalizedA R)) := by
    rw [hcardIndex, ZMod.card]
    omega
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  intro n
  obtain ⟨x, hx, hxuniq⟩ := hbij.existsUnique (n : ZMod (normalizedA R))
  refine ⟨lShapePair (pH R) (qH R) (zH R) (vH R) x,
    ⟨lShapePair_mem x, ?_⟩, ?_⟩
  · exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hx
  · intro ij hij
    obtain ⟨y, hyPair⟩ := exists_lShapeIndex_of_mem hij.1
    have hy : f y = (n : ZMod (normalizedA R)) := by
      apply (ZMod.intCast_eq_intCast_iff _ _ _).2
      simpa [f, lShapeResidue, hyPair] using hij.2
    have hyx : y = x := hxuniq y hy
    calc
      ij = lShapePair (pH R) (qH R) (zH R) (vH R) y := hyPair.symm
      _ = lShapePair (pH R) (qH R) (zH R) (vH R) x := by rw [hyx]

theorem branchB_actual_normalizedA_pos
    (R : SectorBCriticalRoleBranchB P) : 0 < normalizedA R := by
  by_contra hn
  have ha0 : normalizedA R = 0 := Nat.eq_zero_of_not_pos hn
  have hscale := L5A2B4AR3.normalizedWeight_scale P.M.base (R.reindex 0)
  change FourGeneratedBridge.tailGcd _ _ _ * normalizedA R = rawA R at hscale
  rw [ha0, mul_zero] at hscale
  exact (weights_positive P.M.base (R.reindex 0)).ne' hscale.symm

/-- The canonical L-shape representative of an integer, together with the
integer coefficient of the first normalized generator needed for exact
equality (not merely congruence). -/
structure ActualLShapeCoordinate (R : SectorBCriticalRoleBranchB P) (n : ℤ) where
  i : ℤ
  j : ℤ
  level : ℤ
  in_lShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) i j
  exact_eq : n = level * normalizedA R + i * normalizedB R + j * normalizedC R
  level_unique : ∀ level' : ℤ,
    n = level' * normalizedA R + i * normalizedB R + j * normalizedC R →
    level' = level
  pair_unique : ∀ i' j' : ℤ,
    L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) i' j' →
    Int.ModEq (normalizedA R)
      (i' * normalizedB R + j' * normalizedC R) n →
    i' = i ∧ j' = j

noncomputable def branchB_actual_lShape_coordinate
    (R : SectorBCriticalRoleBranchB P) (n : ℤ) :
    ActualLShapeCoordinate R n := by
  let hex := branchB_actual_lShape_coordinates_complete R n
  let ij := Classical.choose hex
  have hij := (Classical.choose_spec hex).1
  have hijUnique := (Classical.choose_spec hex).2
  let hdiv := Int.modEq_iff_dvd.mp hij.2
  let level := Classical.choose hdiv
  have hlevel := Classical.choose_spec hdiv
  exact {
    i := ij.1
    j := ij.2
    level := level
    in_lShape := hij.1
    exact_eq := by nlinarith
    level_unique := by
      intro level' hlevel'
      have hapos : (0 : ℤ) < normalizedA R := by
        exact_mod_cast branchB_actual_normalizedA_pos R
      nlinarith
    pair_unique := by
      intro i' j' hshape hmod
      have hp := hijUnique (i', j') ⟨hshape, hmod⟩
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  }

/-- The three disjoint rectangles constituting the actual Herzog L-shape. -/
inductive ActualLShapeChart
  | center
  | rightBottom
  | leftTop
  deriving DecidableEq

def InActualLShapeChart (R : SectorBCriticalRoleBranchB P)
    (chart : ActualLShapeChart) (i j : ℤ) : Prop :=
  L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) i j ∧
    match chart with
    | .center => i < pH R ∧ j < qH R
    | .rightBottom => pH R ≤ i ∧ j < qH R
    | .leftTop => i < pH R ∧ qH R ≤ j

theorem branchB_actual_center_rb_lt_chart_unique
    (R : SectorBCriticalRoleBranchB P) {i j : ℤ}
    (hshape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) i j) :
    ∃! chart : ActualLShapeChart, InActualLShapeChart R chart i j := by
  rcases hshape with ⟨hi0, hj0, hi, hj, hcorner⟩
  by_cases hip : i < (pH R : ℤ)
  · by_cases hjq : j < (qH R : ℤ)
    · refine ⟨.center, ⟨⟨hi0, hj0, hi, hj, hcorner⟩, hip, hjq⟩, ?_⟩
      intro chart hchart
      rcases chart with _ | _ | _ <;> simp_all [InActualLShapeChart] <;> omega
    · have hqj : (qH R : ℤ) ≤ j := le_of_not_gt hjq
      refine ⟨.leftTop, ⟨⟨hi0, hj0, hi, hj, hcorner⟩, hip, hqj⟩, ?_⟩
      intro chart hchart
      rcases chart with _ | _ | _ <;> simp_all [InActualLShapeChart] <;> omega
  · have hpi : (pH R : ℤ) ≤ i := le_of_not_gt hip
    have hjq : j < (qH R : ℤ) := hcorner.resolve_left hip
    refine ⟨.rightBottom, ⟨⟨hi0, hj0, hi, hj, hcorner⟩, hpi, hjq⟩, ?_⟩
    intro chart hchart
    rcases chart with _ | _ | _ <;> simp_all [InActualLShapeChart] <;> omega

noncomputable def branchB_actual_lShape_chart
    (R : SectorBCriticalRoleBranchB P) {i j : ℤ}
    (hshape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) i j) :
    ActualLShapeChart :=
  Classical.choose (branchB_actual_center_rb_lt_chart_unique R hshape)

theorem branchB_actual_lShape_chart_spec
    (R : SectorBCriticalRoleBranchB P) {i j : ℤ}
    (hshape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) i j) :
    InActualLShapeChart R (branchB_actual_lShape_chart R hshape) i j :=
  (Classical.choose_spec (branchB_actual_center_rb_lt_chart_unique R hshape)).1

/-- Source and complementary-return values of an actual Branch-B birth,
now equipped with canonical L-shape coordinates and exact integer levels. -/
structure ActualPrefixCanonicalLShapeCoordinates
    (R : SectorBCriticalRoleBranchB P) (s : ℤ) where
  data : ActualPrefixSourceCoordinates R s
  source_coordinate : ActualLShapeCoordinate R data.sourceValue
  returned_coordinate : ActualLShapeCoordinate R data.returnedValue
  source_chart : ActualLShapeChart
  source_in_chart :
    InActualLShapeChart R source_chart source_coordinate.i source_coordinate.j
  returned_chart : ActualLShapeChart
  returned_in_chart :
    InActualLShapeChart R returned_chart returned_coordinate.i returned_coordinate.j

noncomputable def branchB_actual_prefix_canonical_lShape_coordinates
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : L5A2B4AR1.IsBranchBirth (L5A2B4AR1.normalizedH P.M.base)
      (L5A2B4AR1.normalizedM P.M.base) (L5A2B4AR1.actualPrincipalIndex P.M.base) s) :
    ActualPrefixCanonicalLShapeCoordinates R s := by
  let data := branchB_actual_prefix_source_coordinates R hB hs
  exact {
    data := data
    source_coordinate := branchB_actual_lShape_coordinate R data.sourceValue
    returned_coordinate := branchB_actual_lShape_coordinate R data.returnedValue
    source_chart := branchB_actual_lShape_chart R
      (branchB_actual_lShape_coordinate R data.sourceValue).in_lShape
    source_in_chart := branchB_actual_lShape_chart_spec R
      (branchB_actual_lShape_coordinate R data.sourceValue).in_lShape
    returned_chart := branchB_actual_lShape_chart R
      (branchB_actual_lShape_coordinate R data.returnedValue).in_lShape
    returned_in_chart := branchB_actual_lShape_chart_spec R
      (branchB_actual_lShape_coordinate R data.returnedValue).in_lShape
  }

end NS25Lean.L5A2B4AR5B
