import NS25Lean.P2BranchBPrefixBranchCount

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}
local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

/-- An actual ordinary zero-set notch: all four points are in L,
southwest is positive, and the other three points are zero. -/
def NonsymmetricOrdinaryNotch (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (x y : ℕ) : Prop :=
  NonsymmetricLDomain R (x+1) (y+1) ∧
  0 < nonsymmetricPrefixDiagramHeight R hB hQ x y ∧
  nonsymmetricPrefixDiagramHeight R hB hQ (x+1) y=0 ∧
  nonsymmetricPrefixDiagramHeight R hB hQ x (y+1)=0 ∧
  nonsymmetricPrefixDiagramHeight R hB hQ (x+1) (y+1)=0

def NonsymmetricOrdinaryNotches (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  {p : ℕ×ℕ // NonsymmetricOrdinaryNotch R hB hQ p.1 p.2}

private theorem domain_down (R : SectorBCriticalRoleBranchB P) {x y x' y' : ℕ}
    (hd : NonsymmetricLDomain R x' y') (hx : x ≤ x') (hy : y ≤ y') :
    NonsymmetricLDomain R x y := by
  unfold NonsymmetricLDomain at *
  rcases hd.2.2 with h | h
  · exact ⟨by omega,by omega,Or.inl (by omega)⟩
  · exact ⟨by omega,by omega,Or.inr (by omega)⟩

theorem nonsymmetric_prefix_ordinary_notch_unused (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {x y : ℕ}
    (hn : NonsymmetricOrdinaryNotch R hB hQ x y) :
    L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (nonsymmetricPrefixRouting R hQ)
      (gridResidue P.M.base (nsReindex R) x y) := by
  obtain ⟨hd,hpos,hSE,hNW,hNE⟩ := hn
  have d0 := domain_down R hd (by omega : x ≤ x+1) (by omega : y ≤ y+1)
  have dB := domain_down R hd (le_refl _) (by omega : y ≤ y+1)
  have dC := domain_down R hd (by omega : x ≤ x+1) (le_refl _)
  have B := nonsymmetric_prefix_b_edge R hB hQ d0 dB (carry:=0) (by ring)
  have C := nonsymmetric_prefix_c_edge R hB hQ d0 dC (carry:=0) (by ring)
  have BC := nonsymmetric_prefix_c_edge R hB hQ dB hd (carry:=0) (by ring)
  have CB := nonsymmetric_prefix_b_edge R hB hQ dC hd (carry:=0) (by ring)
  have hb := B.2; have hc := C.2; have hbc := BC.2; have hcb := CB.2
  rw [hSE] at hb
  rw [hNW] at hc
  rw [hSE,hNE] at hbc
  rw [hNW,hNE] at hcb
  refine ⟨by omega,by omega,?_,?_⟩
  · rw [C.1]; omega
  · rw [B.1]; omega

def nonsymmetricOrdinaryNotchResource (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : NonsymmetricOrdinaryNotches R hB hQ) :
    L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ) :=
  ⟨gridResidue P.M.base (nsReindex R) p.val.1 p.val.2,
    nonsymmetric_prefix_ordinary_notch_unused R hB hQ p.property⟩

theorem nonsymmetricOrdinaryNotchResource_injective (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricOrdinaryNotchResource R hB hQ) := by
  intro p q he
  apply Subtype.ext
  have dp := domain_down R p.property.1 (by omega : p.val.1 ≤ p.val.1+1) (by omega : p.val.2 ≤ p.val.2+1)
  have dq := domain_down R q.property.1 (by omega : q.val.1 ≤ q.val.1+1) (by omega : q.val.2 ≤ q.val.2+1)
  have hc := nonsymmetric_lShape_grid_injective R dp dq (congrArg Subtype.val he)
  exact Prod.ext hc.1 hc.2

theorem nonsymmetric_ordinary_corner_disjoint (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : NonsymmetricOrdinaryNotches R hB hQ) (b : NonsymmetricCornerUnusedTags R hQ) :
    nonsymmetricOrdinaryNotchResource R hB hQ p ≠ nonsymmetricCornerUnusedResource R hQ b := by
  intro he
  have hp := nonsymmetric_coefficients R
  have dp := domain_down R p.property.1 (by omega : p.val.1 ≤ p.val.1+1) (by omega : p.val.2 ≤ p.val.2+1)
  have dom := p.property.1; unfold NonsymmetricLDomain at dom
  have he' := congrArg Subtype.val he
  change gridResidue P.M.base (nsReindex R) p.val.1 p.val.2=nonsymmetricPrefixCorner R b.val at he'
  cases hb : b.val
  · simp only [nonsymmetricPrefixCorner,hb,Bool.false_eq_true,ite_false] at he'
    have dq : NonsymmetricLDomain R (nsP R-1) (nsC3 R-1) := ⟨by omega,by omega,Or.inl (by omega)⟩
    have hc := nonsymmetric_lShape_grid_injective R dp dq he'
    omega
  · simp only [nonsymmetricPrefixCorner,hb,ite_true] at he'
    have dq : NonsymmetricLDomain R (nsC2 R-1) (nsQ R-1) := ⟨by omega,by omega,Or.inr (by omega)⟩
    have hc := nonsymmetric_lShape_grid_injective R dp dq he'
    omega

def nonsymmetricPrefixUnusedResource (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    NonsymmetricOrdinaryNotches R hB hQ ⊕ NonsymmetricCornerUnusedTags R hQ →
      L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ) :=
  Sum.elim (nonsymmetricOrdinaryNotchResource R hB hQ) (nonsymmetricCornerUnusedResource R hQ)

theorem nonsymmetricPrefixUnusedResource_injective (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricPrefixUnusedResource R hB hQ) := by
  intro x y he
  cases x with
  | inl p =>
    cases y with
    | inl q => exact congrArg Sum.inl (nonsymmetricOrdinaryNotchResource_injective R hB hQ he)
    | inr b => exact (nonsymmetric_ordinary_corner_disjoint R hB hQ p b he).elim
  | inr b =>
    cases y with
    | inl p => exact (nonsymmetric_ordinary_corner_disjoint R hB hQ p b he.symm).elim
    | inr c => exact congrArg Sum.inr (nonsymmetricCornerUnusedResource_injective R hQ he)

theorem nonsymmetric_prefix_unused_count_ge_notches_FU (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    Nat.card (NonsymmetricOrdinaryNotches R hB hQ)+nonsymmetricFU R hB ≤
      Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ)) := by
  letI : Finite (L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ)) := Subtype.finite
  letI : Finite (NonsymmetricOrdinaryNotches R hB hQ) :=
    Finite.of_injective _ (nonsymmetricOrdinaryNotchResource_injective R hB hQ)
  letI : Finite (NonsymmetricCornerUnusedTags R hQ) :=
    Finite.of_injective _ (nonsymmetricCornerUnusedResource_injective R hQ)
  have hm := Nat.card_le_card_of_injective _ (nonsymmetricPrefixUnusedResource_injective R hB hQ)
  simpa only [Nat.card_sum,nonsymmetric_corner_unused_tag_count R hB hQ hbal] using hm

end NS25Lean.L5A2BFinalRepair
