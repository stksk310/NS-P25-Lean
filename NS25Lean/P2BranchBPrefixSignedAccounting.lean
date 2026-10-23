import NS25Lean.P2BranchBMixedSurgery

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

theorem nonsymmetricReturnIndex_finite (R : SectorBCriticalRoleBranchB P) :
    Finite (NonsymmetricReturnIndex R) := by
  let f : NonsymmetricReturnIndex R → Fin (actualPrincipalIndex P.M.base) :=
    fun ell => ⟨ell.val,ell.property.2⟩
  apply Finite.of_injective f
  intro x y he
  exact Subtype.ext (congrArg Fin.val he)

/-- Actual maximum of return depths on a specified subfamily; empty means zero. -/
def nonsymmetricReturnDepthMax (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (p : NonsymmetricReturnIndex R → Prop) : ℕ := by
  letI := nonsymmetricReturnIndex_finite R
  letI := Fintype.ofFinite (NonsymmetricReturnIndex R)
  exact Finset.univ.sup (fun ell => if p ell then (nonsymmetricReturnTuple R hB ell).2.2 else 0)

theorem nonsymmetricReturnDepthMax_mono (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    {p q : NonsymmetricReturnIndex R → Prop} (hpq : ∀ ell, p ell → q ell) :
    nonsymmetricReturnDepthMax R hB p ≤ nonsymmetricReturnDepthMax R hB q := by
  letI := nonsymmetricReturnIndex_finite R
  letI := Fintype.ofFinite (NonsymmetricReturnIndex R)
  unfold nonsymmetricReturnDepthMax
  apply Finset.sup_le
  intro ell hell
  by_cases hp : p ell
  · simp only [ite_eq_left hp]
    have hq := hpq ell hp
    simpa only [ite_eq_left hq] using (Finset.le_sup (f:=fun ell =>
      if q ell then (nonsymmetricReturnTuple R hB ell).2.2 else 0) hell)
  · simp only [ite_eq_right hp]
    exact Nat.zero_le _

abbrev nonsymmetricDL (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :=
  nonsymmetricReturnDepthMax R hB (fun ell => (nonsymmetricReturnTuple R hB ell).1 < nsP R)
abbrev nonsymmetricDR (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :=
  nonsymmetricReturnDepthMax R hB (fun ell => (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R)
abbrev nonsymmetricDL0 (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :=
  nonsymmetricReturnDepthMax R hB (fun ell => (nonsymmetricReturnTuple R hB ell).2.1 = nsQ R)
abbrev nonsymmetricDR0 (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :=
  nonsymmetricReturnDepthMax R hB (fun ell => (nonsymmetricReturnTuple R hB ell).1 = nsP R)

theorem nonsymmetric_boundary_depth_maxima_le (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) :
    nonsymmetricDL0 R hB ≤ nonsymmetricDL R hB ∧
      nonsymmetricDR0 R hB ≤ nonsymmetricDR R hB := by
  constructor
  · apply nonsymmetricReturnDepthMax_mono
    intro ell he
    have hd := (nonsymmetricReturnTuple_spec R hB ell).1.2.2
    omega
  · apply nonsymmetricReturnDepthMax_mono
    intro ell he
    have hd := (nonsymmetricReturnTuple_spec R hB ell).1.2.2
    omega

/-- N7's actual return-depth quantity. Its identification with prefix fake
corners carrying extra U-tags is not assumed or stored in the data. -/
def nonsymmetricFU (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) : ℕ :=
  (if nonsymmetricDL0 R hB ≤ nonsymmetricDR R hB then 1 else 0)+
    (if nonsymmetricDR0 R hB ≤ nonsymmetricDL R hB then 1 else 0)

theorem nonsymmetric_FU_one_or_two (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :
    nonsymmetricFU R hB=1 ∨ nonsymmetricFU R hB=2 := by
  have hm := nonsymmetric_boundary_depth_maxima_le R hB
  unfold nonsymmetricFU
  split_ifs <;> omega

def nonsymmetricPrefixSlack (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) : ℤ :=
  (Nat.card {w // IsIntegralSocle (nonsymmetricPrefixIdeal R hQ) w} : ℤ)-
    (nonsymmetricPrefixIdeal R hQ).generatorCount

def nonsymmetricDeltaSocle (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) : ℤ :=
  (Gamma.asRelativeIdeal.idealType : ℤ)-
    Nat.card {w // IsIntegralSocle (nonsymmetricPrefixIdeal R hQ) w}

def nonsymmetricDeltaSource (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) : ℤ :=
  (P.sourceCount : ℤ)-(nonsymmetricPrefixIdeal R hQ).generatorCount

theorem nonsymmetric_DeltaSocle_le_two (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) : nonsymmetricDeltaSocle R hQ ≤ 2 := by
  have hh := nonsymmetric_principal_socle_gain_le_two R hB hQ
  unfold nonsymmetricDeltaSocle
  omega

/-- Exact signed accounting; no truncated natural subtraction. -/
theorem nonsymmetric_signed_defect_identity (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    (P.W : ℤ)=nonsymmetricPrefixSlack R hQ+nonsymmetricDeltaSocle R hQ-
      nonsymmetricDeltaSource R hQ := by
  unfold nonsymmetricPrefixSlack nonsymmetricDeltaSocle nonsymmetricDeltaSource
  rw [P2Data.W]
  ring

end NS25Lean.L5A2BFinalRepair
