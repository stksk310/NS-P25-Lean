import NS25Lean.P2CriticalRoleDichotomy

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR4R2B

open ChosenBase L2B L5A1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

abbrev c1 (R : SectorBCriticalRoleBranchB P) : ℕ :=
  criticalExponent P.M.base (R.reindex 0)

abbrev c2 (R : SectorBCriticalRoleBranchB P) : ℕ :=
  criticalExponent P.M.base (R.reindex 1)

abbrev r12 (R : SectorBCriticalRoleBranchB P) : ℕ :=
  R.first.witness.val (R.reindex 1)

abbrev r13 (R : SectorBCriticalRoleBranchB P) : ℕ :=
  R.first.witness.val (R.reindex 2)

abbrev r21 (R : SectorBCriticalRoleBranchB P) : ℕ :=
  R.second.witness.val (R.reindex 0)

abbrev r23 (R : SectorBCriticalRoleBranchB P) : ℕ :=
  R.second.witness.val (R.reindex 2)

abbrev r31 (R : SectorBCriticalRoleBranchB P) : ℕ := c1 R - r21 R
abbrev r32 (R : SectorBCriticalRoleBranchB P) : ℕ := c2 R - r12 R
abbrev c3 (R : SectorBCriticalRoleBranchB P) : ℕ := r13 R + r23 R

private theorem outside_zero_of_relation (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    {q x y : ℕ} (hq : 0 < q)
    (h : q * weights B (e 0) = x * weights B (e 1) + y * weights B (e 2)) :
    OutsideExponent B (e 0) q := by
  refine ⟨hq, Finsupp.single (e 1) x + Finsupp.single (e 2) y, ?_, ?_⟩
  · simp
  · simpa [map_add, weight_single] using h.symm

private theorem outside_one_of_relation (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    {q x y : ℕ} (hq : 0 < q)
    (h : q * weights B (e 1) = x * weights B (e 0) + y * weights B (e 2)) :
    OutsideExponent B (e 1) q := by
  refine ⟨hq, Finsupp.single (e 0) x + Finsupp.single (e 2) y, ?_, ?_⟩
  · simp
  · simpa [map_add, weight_single] using h.symm

private theorem outside_two_of_relation (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    {q x y : ℕ} (hq : 0 < q)
    (h : q * weights B (e 2) = x * weights B (e 0) + y * weights B (e 1)) :
    OutsideExponent B (e 2) q := by
  refine ⟨hq, Finsupp.single (e 0) x + Finsupp.single (e 1) y, ?_, ?_⟩
  · simp
  · simpa [map_add, weight_single] using h.symm

theorem branchB_first_relation (R : SectorBCriticalRoleBranchB P) :
    c1 R * weights P.M.base (R.reindex 0) =
      r12 R * weights P.M.base (R.reindex 1) +
        r13 R * weights P.M.base (R.reindex 2) := by
  calc
    c1 R * weights P.M.base (R.reindex 0) = R.firstDegree := by
      simpa [c1, R.reindex_zero] using R.first.degree_eq_critical.symm
    _ = weight P.M.base R.first.witness.val := R.first.witness.property.symm
    _ = R.first.witness.val (R.reindex 0) * weights P.M.base (R.reindex 0) +
        R.first.witness.val (R.reindex 1) * weights P.M.base (R.reindex 1) +
        R.first.witness.val (R.reindex 2) * weights P.M.base (R.reindex 2) :=
      L5A2B4AR3.weight_three_coordinates P.M.base R.reindex R.first.witness.val
    _ = r12 R * weights P.M.base (R.reindex 1) +
        r13 R * weights P.M.base (R.reindex 2) := by
      have hz : R.first.witness.val (R.reindex 0) = 0 := by
        rw [R.reindex_zero]
        exact R.first.witness_pure_zero
      simp [hz]

theorem branchB_second_relation (R : SectorBCriticalRoleBranchB P) :
    c2 R * weights P.M.base (R.reindex 1) =
      r21 R * weights P.M.base (R.reindex 0) +
        r23 R * weights P.M.base (R.reindex 2) := by
  calc
    c2 R * weights P.M.base (R.reindex 1) = R.secondDegree := by
      simpa [c2, R.reindex_one] using R.second.degree_eq_critical.symm
    _ = weight P.M.base R.second.witness.val := R.second.witness.property.symm
    _ = R.second.witness.val (R.reindex 0) * weights P.M.base (R.reindex 0) +
        R.second.witness.val (R.reindex 1) * weights P.M.base (R.reindex 1) +
        R.second.witness.val (R.reindex 2) * weights P.M.base (R.reindex 2) :=
      L5A2B4AR3.weight_three_coordinates P.M.base R.reindex R.second.witness.val
    _ = r21 R * weights P.M.base (R.reindex 0) +
        r23 R * weights P.M.base (R.reindex 2) := by
      have hz : R.second.witness.val (R.reindex 1) = 0 := by
        rw [R.reindex_one]
        exact R.second.witness_pure_zero
      simp [hz]

theorem branchB_cross_coefficients_positive (R : SectorBCriticalRoleBranchB P) :
    0 < r12 R ∧ 0 < r13 R ∧ 0 < r21 R ∧ 0 < r23 R :=
  ⟨R.first_witness_one_pos, R.first_witness_two_pos,
    R.second_witness_zero_pos, R.second_witness_two_pos⟩

theorem branchB_cross_inequalities (R : SectorBCriticalRoleBranchB P) :
    r21 R < c1 R ∧ r12 R < c2 R := by
  let a := weights P.M.base (R.reindex 0)
  let b := weights P.M.base (R.reindex 1)
  let c := weights P.M.base (R.reindex 2)
  have ha : 0 < a := weights_positive P.M.base (R.reindex 0)
  have hb : 0 < b := weights_positive P.M.base (R.reindex 1)
  have hc : 0 < c := weights_positive P.M.base (R.reindex 2)
  have h1 := branchB_first_relation R
  have h2 := branchB_second_relation R
  obtain ⟨hr12, hr13, hr21, hr23⟩ := branchB_cross_coefficients_positive R
  constructor
  · by_contra hn
    have hle : c1 R ≤ r21 R := by omega
    have hlt : r12 R < c2 R := by
      dsimp [a, b, c] at ha hb hc h1 h2 ⊢
      nlinarith
    have hsub1 : c2 R - r12 R + r12 R = c2 R := Nat.sub_add_cancel (le_of_lt hlt)
    have hsub2 : r21 R - c1 R + c1 R = r21 R := Nat.sub_add_cancel hle
    have hrel : (c2 R - r12 R) * b =
        (r21 R - c1 R) * a + (r13 R + r23 R) * c := by
      dsimp [a, b, c] at h1 h2 ⊢
      nlinarith
    have hq : 0 < c2 R - r12 R := Nat.sub_pos_of_lt hlt
    have hmin := criticalExponent_min P.M.base (R.reindex 1) (c2 R - r12 R)
      (outside_one_of_relation P.M.base R.reindex hq hrel)
    change c2 R ≤ c2 R - r12 R at hmin
    exact (Nat.not_lt_of_ge hmin) (by omega)
  · by_contra hn
    have hle : c2 R ≤ r12 R := by omega
    have hlt : r21 R < c1 R := by
      dsimp [a, b, c] at ha hb hc h1 h2 ⊢
      nlinarith
    have hsub1 : c1 R - r21 R + r21 R = c1 R := Nat.sub_add_cancel (le_of_lt hlt)
    have hsub2 : r12 R - c2 R + c2 R = r12 R := Nat.sub_add_cancel hle
    have hrel : (c1 R - r21 R) * a =
        (r12 R - c2 R) * b + (r13 R + r23 R) * c := by
      dsimp [a, b, c] at h1 h2 ⊢
      nlinarith
    have hq : 0 < c1 R - r21 R := Nat.sub_pos_of_lt hlt
    have hmin := criticalExponent_min P.M.base (R.reindex 0) (c1 R - r21 R)
      (outside_zero_of_relation P.M.base R.reindex hq hrel)
    change c1 R ≤ c1 R - r21 R at hmin
    exact (Nat.not_lt_of_ge hmin) (by omega)

theorem branchB_third_candidate_relation (R : SectorBCriticalRoleBranchB P) :
    0 < r31 R ∧ 0 < r32 R ∧ 0 < c3 R ∧
      c3 R * weights P.M.base (R.reindex 2) =
        r31 R * weights P.M.base (R.reindex 0) +
          r32 R * weights P.M.base (R.reindex 1) := by
  obtain ⟨h21, h12⟩ := branchB_cross_inequalities R
  obtain ⟨hr12, hr13, hr21, hr23⟩ := branchB_cross_coefficients_positive R
  have h1 := branchB_first_relation R
  have h2 := branchB_second_relation R
  have hs1 : r31 R + r21 R = c1 R := Nat.sub_add_cancel (le_of_lt h21)
  have hs2 : r32 R + r12 R = c2 R := Nat.sub_add_cancel (le_of_lt h12)
  refine ⟨Nat.sub_pos_of_lt h21, Nat.sub_pos_of_lt h12,
    Nat.add_pos_left hr13 _, ?_⟩
  dsimp [r31, r32, c3] at hs1 hs2 ⊢
  nlinarith

/-- Pure arithmetic core of the third-criticality argument.  The three
minimality hypotheses are the defining minimality of the three actual
critical exponents; no third relation is assumed. -/
private theorem third_critical_of_two_mixed
    (a b c c1' c2' d r12' r13' r21' r23' x y : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hr12 : 0 < r12') (hr13 : 0 < r13')
    (hr21 : 0 < r21')
    (h21 : r21' < c1') (h12 : r12' < c2')
    (h1 : c1' * a = r12' * b + r13' * c)
    (h2 : c2' * b = r21' * a + r23' * c)
    (hdrel : d * c = x * a + y * b)
    (hmin1 : ∀ q u v : ℕ, 0 < q → q * a = u * b + v * c → c1' ≤ q)
    (hmin2 : ∀ q u v : ℕ, 0 < q → q * b = u * a + v * c → c2' ≤ q)
    (hmin3 : ∀ q u v : ℕ, 0 < q → q * c = u * a + v * b → d ≤ q) :
    d = r13' + r23' := by
  let r31' := c1' - r21'
  let r32' := c2' - r12'
  let c3' := r13' + r23'
  have hr31 : 0 < r31' := Nat.sub_pos_of_lt h21
  have hr32 : 0 < r32' := Nat.sub_pos_of_lt h12
  have hc3 : 0 < c3' := Nat.add_pos_left hr13 _
  have hs1 : r31' + r21' = c1' := Nat.sub_add_cancel (le_of_lt h21)
  have hs2 : r32' + r12' = c2' := Nat.sub_add_cancel (le_of_lt h12)
  have hcand : c3' * c = r31' * a + r32' * b := by
    dsimp [r31', r32', c3'] at hs1 hs2 ⊢
    nlinarith only [h1, h2, hs1, hs2]
  have hdle : d ≤ c3' := hmin3 c3' r31' r32' hc3 hcand
  by_contra hne
  have hdc3 : d < c3' := by omega
  have hbounds : ∀ n : ℕ, n * d < c3' → n * x < r31' ∧ n * y < r32' := by
    intro n hn
    have hdn : (n * d) * c = (n * x) * a + (n * y) * b := by
      calc
        (n * d) * c = n * (d * c) := by ring
        _ = n * (x * a + y * b) := by rw [hdrel]
        _ = (n * x) * a + (n * y) * b := by ring
    constructor
    · by_contra hnx
      have hxge : r31' ≤ n * x := by omega
      have hylt : n * y < r32' := by
        by_contra hny
        have hyge : r32' ≤ n * y := by omega
        nlinarith only [hcand, hdn, hxge, hyge, hn, hc]
      have hsx : n * x - r31' + r31' = n * x := Nat.sub_add_cancel hxge
      have hsy : r32' - n * y + n * y = r32' :=
        Nat.sub_add_cancel (le_of_lt hylt)
      have hsc : c3' - n * d + n * d = c3' :=
        Nat.sub_add_cancel (le_of_lt hn)
      have hrel : (r32' - n * y) * b =
          (n * x - r31') * a + (c3' - n * d) * c := by
        nlinarith only [hcand, hdn, hsx, hsy, hsc]
      have hq : 0 < r32' - n * y := Nat.sub_pos_of_lt hylt
      have hm := hmin2 (r32' - n * y) (n * x - r31') (c3' - n * d) hq hrel
      have hqle : r32' - n * y ≤ r32' := Nat.sub_le _ _
      omega
    · by_contra hny
      have hyge : r32' ≤ n * y := by omega
      have hxlt : n * x < r31' := by
        by_contra hnx
        have hxge : r31' ≤ n * x := by omega
        nlinarith only [hcand, hdn, hxge, hyge, hn, hc]
      have hsy : n * y - r32' + r32' = n * y := Nat.sub_add_cancel hyge
      have hsx : r31' - n * x + n * x = r31' :=
        Nat.sub_add_cancel (le_of_lt hxlt)
      have hsc : c3' - n * d + n * d = c3' :=
        Nat.sub_add_cancel (le_of_lt hn)
      have hrel : (r31' - n * x) * a =
          (n * y - r32') * b + (c3' - n * d) * c := by
        nlinarith only [hcand, hdn, hsx, hsy, hsc]
      have hq : 0 < r31' - n * x := Nat.sub_pos_of_lt hxlt
      have hm := hmin1 (r31' - n * x) (n * y - r32') (c3' - n * d) hq hrel
      have hqle : r31' - n * x ≤ r31' := Nat.sub_le _ _
      omega
  let k := c3' / d
  let rem := c3' % d
  have hdecomp : rem + d * k = c3' := by
    simpa [k, rem] using Nat.mod_add_div c3' d
  have hrem : rem = 0 := by
    by_contra hrem0
    have hrempos : 0 < rem := Nat.pos_of_ne_zero hrem0
    have hremd : rem < d := by
      dsimp [rem]
      exact Nat.mod_lt _ hd
    have hkd : k * d < c3' := by nlinarith only [hdecomp, hrempos]
    obtain ⟨hkx, hky⟩ := hbounds k hkd
    have hdn : (k * d) * c = (k * x) * a + (k * y) * b := by
      calc
        (k * d) * c = k * (d * c) := by ring
        _ = k * (x * a + y * b) := by rw [hdrel]
        _ = (k * x) * a + (k * y) * b := by ring
    have hsx : r31' - k * x + k * x = r31' := Nat.sub_add_cancel (le_of_lt hkx)
    have hsy : r32' - k * y + k * y = r32' := Nat.sub_add_cancel (le_of_lt hky)
    have hrel : rem * c = (r31' - k * x) * a + (r32' - k * y) * b := by
      nlinarith only [hcand, hdn, hdecomp, hsx, hsy]
    have hm := hmin3 rem (r31' - k * x) (r32' - k * y) hrempos hrel
    omega
  have hc3kd : c3' = k * d := by nlinarith only [hdecomp, hrem]
  have hkpos : 0 < k := by
    by_contra hk
    have : k = 0 := Nat.eq_zero_of_not_pos hk
    simp [this] at hc3kd
    omega
  have hktwo : 2 ≤ k := by nlinarith only [hc3kd, hdc3, hd]
  have hkpred : (k - 1) * d < c3' := by
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    nlinarith only [hk1, hc3kd, hd]
  obtain ⟨hxpred, hypred⟩ := hbounds (k - 1) hkpred
  have hkrel : (k * x) * a + (k * y) * b = r31' * a + r32' * b := by
    have hdn : (k * d) * c = (k * x) * a + (k * y) * b := by
      calc
        (k * d) * c = k * (d * c) := by ring
        _ = k * (x * a + y * b) := by rw [hdrel]
        _ = (k * x) * a + (k * y) * b := by ring
    nlinarith only [hdn, hcand, hc3kd]
  have hxscale : k * x = r31' := by
    rcases lt_trichotomy (k * x) r31' with hxlt | hxeq | hxgt
    · have hygt : r32' < k * y := by
        by_contra hny
        have hnyle : k * y ≤ r32' := by omega
        have hxa : (k * x) * a < r31' * a := Nat.mul_lt_mul_of_pos_right hxlt ha
        have hyb : (k * y) * b ≤ r32' * b := Nat.mul_le_mul_right b hnyle
        omega
      have hsx : r31' - k * x + k * x = r31' :=
        Nat.sub_add_cancel (le_of_lt hxlt)
      have hsy : k * y - r32' + r32' = k * y :=
        Nat.sub_add_cancel (le_of_lt hygt)
      have hrel : (k * y - r32') * b = (r31' - k * x) * a + 0 * c := by
        nlinarith only [hkrel, hsx, hsy]
      have hq : 0 < k * y - r32' := Nat.sub_pos_of_lt hygt
      have hm := hmin2 (k * y - r32') (r31' - k * x) 0 hq hrel
      have hsmall : k * y - r32' < c2' := by
        have hkexpand : k * y = (k - 1) * y + y := by
          have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
          nlinarith only [hk1]
        nlinarith only [hypred, hkexpand, hsy, hs2, hr12, hktwo]
      omega
    · exact hxeq
    · have hylt : k * y < r32' := by
        by_contra hny
        have hnyge : r32' ≤ k * y := by omega
        have hxa : r31' * a < (k * x) * a := Nat.mul_lt_mul_of_pos_right hxgt ha
        have hyb : r32' * b ≤ (k * y) * b := Nat.mul_le_mul_right b hnyge
        omega
      have hsx : k * x - r31' + r31' = k * x :=
        Nat.sub_add_cancel (le_of_lt hxgt)
      have hsy : r32' - k * y + k * y = r32' :=
        Nat.sub_add_cancel (le_of_lt hylt)
      have hrel : (k * x - r31') * a = (r32' - k * y) * b + 0 * c := by
        nlinarith only [hkrel, hsx, hsy]
      have hq : 0 < k * x - r31' := Nat.sub_pos_of_lt hxgt
      have hm := hmin1 (k * x - r31') (r32' - k * y) 0 hq hrel
      have hsmall : k * x - r31' < c1' := by
        have hkexpand : k * x = (k - 1) * x + x := by
          have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
          nlinarith only [hk1]
        nlinarith only [hxpred, hkexpand, hsx, hs1, hr21, hktwo]
      omega
  have hyscale : k * y = r32' := by nlinarith only [hkrel, hxscale, hb]
  have hxpos : 0 < x := by
    by_contra hx
    have : x = 0 := Nat.eq_zero_of_not_pos hx
    simp [this] at hxscale
    omega
  have hypos : 0 < y := by
    by_contra hy
    have : y = 0 := Nat.eq_zero_of_not_pos hy
    simp [this] at hyscale
    omega
  have hr13d : r13' < d := by
    by_contra hn
    have hle : d ≤ r13' := by omega
    have hxlt : x < c1' := by nlinarith only [hxscale, hs1, hr21, hkpos]
    have hsx : c1' - x + x = c1' := Nat.sub_add_cancel (le_of_lt hxlt)
    have hsr : r13' - d + d = r13' := Nat.sub_add_cancel hle
    have hrel : (c1' - x) * a = (r12' + y) * b + (r13' - d) * c := by
      nlinarith only [h1, hdrel, hsx, hsr]
    have hq : 0 < c1' - x := Nat.sub_pos_of_lt hxlt
    have hm := hmin1 (c1' - x) (r12' + y) (r13' - d) hq hrel
    omega
  have hr23d : r23' < d := by
    by_contra hn
    have hle : d ≤ r23' := by omega
    have hylt : y < c2' := by nlinarith only [hyscale, hs2, hr12, hkpos]
    have hsy : c2' - y + y = c2' := Nat.sub_add_cancel (le_of_lt hylt)
    have hsr : r23' - d + d = r23' := Nat.sub_add_cancel hle
    have hrel : (c2' - y) * b = (r21' + x) * a + (r23' - d) * c := by
      nlinarith only [h2, hdrel, hsy, hsr]
    have hq : 0 < c2' - y := Nat.sub_pos_of_lt hylt
    have hm := hmin2 (c2' - y) (r21' + x) (r23' - d) hq hrel
    omega
  dsimp [c3'] at hc3kd
  nlinarith only [hr13d, hr23d, hc3kd, hktwo, hd]

theorem branchB_third_criticalExponent (R : SectorBCriticalRoleBranchB P) :
    criticalExponent P.M.base (R.reindex 2) = c3 R := by
  let a := weights P.M.base (R.reindex 0)
  let b := weights P.M.base (R.reindex 1)
  let c := weights P.M.base (R.reindex 2)
  let d := criticalExponent P.M.base (R.reindex 2)
  obtain ⟨hd, v, hvzero, hvweight⟩ := criticalExponent_spec P.M.base (R.reindex 2)
  have hdrel : d * c = v (R.reindex 0) * a + v (R.reindex 1) * b := by
    have hexpand := L5A2B4AR3.weight_three_coordinates P.M.base R.reindex v
    dsimp [d, c, a, b]
    rw [hexpand, hvzero, zero_mul, add_zero] at hvweight
    exact hvweight.symm
  have hmin1 : ∀ q u w : ℕ, 0 < q → q * a = u * b + w * c → c1 R ≤ q := by
    intro q u w hq hrel
    exact criticalExponent_min P.M.base (R.reindex 0) q
      (outside_zero_of_relation P.M.base R.reindex hq hrel)
  have hmin2 : ∀ q u w : ℕ, 0 < q → q * b = u * a + w * c → c2 R ≤ q := by
    intro q u w hq hrel
    exact criticalExponent_min P.M.base (R.reindex 1) q
      (outside_one_of_relation P.M.base R.reindex hq hrel)
  have hmin3 : ∀ q u w : ℕ, 0 < q → q * c = u * a + w * b → d ≤ q := by
    intro q u w hq hrel
    exact criticalExponent_min P.M.base (R.reindex 2) q
      (outside_two_of_relation P.M.base R.reindex hq hrel)
  obtain ⟨h21, h12⟩ := branchB_cross_inequalities R
  obtain ⟨hr12, hr13, hr21, hr23⟩ := branchB_cross_coefficients_positive R
  have h1 := branchB_first_relation R
  have h2 := branchB_second_relation R
  apply third_critical_of_two_mixed a b c (c1 R) (c2 R) d
    (r12 R) (r13 R) (r21 R) (r23 R) (v (R.reindex 0)) (v (R.reindex 1))
  · exact weights_positive P.M.base (R.reindex 0)
  · exact weights_positive P.M.base (R.reindex 1)
  · exact weights_positive P.M.base (R.reindex 2)
  · exact hd
  · exact hr12
  · exact hr13
  · exact hr21
  · exact h21
  · exact h12
  · exact h1
  · exact h2
  · exact hdrel
  · exact hmin1
  · exact hmin2
  · exact hmin3

def thirdWitness (R : SectorBCriticalRoleBranchB P) : Fin 3 →₀ ℕ :=
  Finsupp.single (R.reindex 0) (r31 R) + Finsupp.single (R.reindex 1) (r32 R)

theorem thirdWitness_weight (R : SectorBCriticalRoleBranchB P) :
    weight P.M.base (thirdWitness R) =
      criticalExponent P.M.base (R.reindex 2) * weights P.M.base (R.reindex 2) := by
  rw [branchB_third_criticalExponent R]
  obtain ⟨_, _, _, hrel⟩ := branchB_third_candidate_relation R
  change weight P.M.base
      (Finsupp.single (R.reindex 0) (r31 R) +
        Finsupp.single (R.reindex 1) (r32 R)) = _
  rw [map_add, weight_single, weight_single]
  exact hrel.symm

def thirdCriticalFactorization (R : SectorBCriticalRoleBranchB P) :
    FactorizationFiber P.M.base
      (criticalExponent P.M.base (R.reindex 2) * weights P.M.base (R.reindex 2)) :=
  ⟨thirdWitness R, thirdWitness_weight R⟩

theorem branchB_actual_third_mixed_witness (R : SectorBCriticalRoleBranchB P) :
    (thirdCriticalFactorization R).val (R.reindex 2) = 0 ∧
      (thirdCriticalFactorization R).val (R.reindex 0) = r31 R ∧
      (thirdCriticalFactorization R).val (R.reindex 1) = r32 R ∧
      0 < (thirdCriticalFactorization R).val (R.reindex 0) ∧
      0 < (thirdCriticalFactorization R).val (R.reindex 1) ∧
      (thirdCriticalFactorization R).val.support = {R.reindex 0, R.reindex 1} := by
  classical
  obtain ⟨hr31, hr32, _, _⟩ := branchB_third_candidate_relation R
  have h20 : R.reindex 2 ≠ R.reindex 0 := R.reindex.injective.ne (by decide)
  have h21 : R.reindex 2 ≠ R.reindex 1 := R.reindex.injective.ne (by decide)
  have h01 : R.reindex 0 ≠ R.reindex 1 := R.reindex.injective.ne (by decide)
  refine ⟨by simp [thirdCriticalFactorization, thirdWitness, h20, h21],
    by simp [thirdCriticalFactorization, thirdWitness, h01],
    by simp [thirdCriticalFactorization, thirdWitness, Ne.symm h01],
    by simpa [thirdCriticalFactorization, thirdWitness, h01] using hr31,
    by simpa [thirdCriticalFactorization, thirdWitness, Ne.symm h01] using hr32, ?_⟩
  ext i
  obtain ⟨j, rfl⟩ := R.reindex.surjective i
  fin_cases j <;>
    simp [thirdCriticalFactorization, thirdWitness, hr31.ne', hr32.ne',
      R.reindex.injective.eq_iff]

structure NonsymmetricHerzogCompletion (R : SectorBCriticalRoleBranchB P) : Prop where
  cross_positive :
    0 < r12 R ∧ 0 < r13 R ∧ 0 < r21 R ∧ 0 < r23 R ∧ 0 < r31 R ∧ 0 < r32 R
  coefficient_sums :
    c1 R = r21 R + r31 R ∧ c2 R = r12 R + r32 R ∧ c3 R = r13 R + r23 R
  weighted_relations :
    c1 R * weights P.M.base (R.reindex 0) =
        r12 R * weights P.M.base (R.reindex 1) +
          r13 R * weights P.M.base (R.reindex 2) ∧
      c2 R * weights P.M.base (R.reindex 1) =
        r21 R * weights P.M.base (R.reindex 0) +
          r23 R * weights P.M.base (R.reindex 2) ∧
      c3 R * weights P.M.base (R.reindex 2) =
        r31 R * weights P.M.base (R.reindex 0) +
          r32 R * weights P.M.base (R.reindex 1)
  third_critical : criticalExponent P.M.base (R.reindex 2) = c3 R
  third_witness_self_zero : (thirdCriticalFactorization R).val (R.reindex 2) = 0
  third_witness_zero_eq : (thirdCriticalFactorization R).val (R.reindex 0) = r31 R
  third_witness_one_eq : (thirdCriticalFactorization R).val (R.reindex 1) = r32 R
  third_witness_zero_pos : 0 < (thirdCriticalFactorization R).val (R.reindex 0)
  third_witness_one_pos : 0 < (thirdCriticalFactorization R).val (R.reindex 1)
  third_witness_support :
    (thirdCriticalFactorization R).val.support = {R.reindex 0, R.reindex 1}

theorem branchB_nonsymmetric_herzog_completion (R : SectorBCriticalRoleBranchB P) :
    NonsymmetricHerzogCompletion R := by
  obtain ⟨hr12, hr13, hr21, hr23⟩ := branchB_cross_coefficients_positive R
  obtain ⟨h21, h12⟩ := branchB_cross_inequalities R
  obtain ⟨hr31, hr32, hc3, h3⟩ := branchB_third_candidate_relation R
  obtain ⟨hw2, hw0, hw1, hw0pos, hw1pos, hsupport⟩ :=
    branchB_actual_third_mixed_witness R
  refine {
    cross_positive := ⟨hr12, hr13, hr21, hr23, hr31, hr32⟩
    coefficient_sums := ⟨?_, ?_, rfl⟩
    weighted_relations := ⟨branchB_first_relation R, branchB_second_relation R, h3⟩
    third_critical := branchB_third_criticalExponent R
    third_witness_self_zero := hw2
    third_witness_zero_eq := hw0
    third_witness_one_eq := hw1
    third_witness_zero_pos := hw0pos
    third_witness_one_pos := hw1pos
    third_witness_support := hsupport
  }
  · exact (Nat.sub_add_cancel (le_of_lt h21)).symm.trans (Nat.add_comm _ _)
  · exact (Nat.sub_add_cancel (le_of_lt h12)).symm.trans (Nat.add_comm _ _)

end NS25Lean.L5A2B4AR4R2B
