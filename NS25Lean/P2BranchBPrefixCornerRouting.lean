import NS25Lean.P2BranchBPrefixCornerHeights

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}
local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

def nonsymmetricPrefixRouting (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) : CombinatorialCore.ResidueData (ZMod (nsA R)) :=
  ((nonsymmetricPrefixIdeal R hQ).toAperyStepData (nsA R) (nsB R) (nsC R)
    (routingHB _ _) (routingHC _ _)).toResidueData
    ((nonsymmetricPrefixIdeal R hQ).toAperyStepData_isValid (nsA R) (nsB R) (nsC R)
      (routingHB _ _) (routingHC _ _))

abbrev nonsymmetricKappa1 (R : SectorBCriticalRoleBranchB P) :=
  gridResidue P.M.base (nsReindex R) (nsC2 R-1) (nsQ R-1)
abbrev nonsymmetricKappa2 (R : SectorBCriticalRoleBranchB P) :=
  gridResidue P.M.base (nsReindex R) (nsP R-1) (nsC3 R-1)

theorem nonsymmetric_prefix_b_edge (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {x y x' y' carry : ℕ}
    (hd : NonsymmetricLDomain R x y) (hd' : NonsymmetricLDomain R x' y')
    (he : x*nsB R+y*nsC R+nsB R=carry*nsA R+x'*nsB R+y'*nsC R) :
    (nonsymmetricPrefixRouting R hQ).b (gridResidue P.M.base (nsReindex R) x y)=
      gridResidue P.M.base (nsReindex R) x' y' ∧
    (nonsymmetricPrefixRouting R hQ).u (gridResidue P.M.base (nsReindex R) x y)+
      nonsymmetricPrefixDiagramHeight R hB hQ x' y'=
      nonsymmetricPrefixDiagramHeight R hB hQ x y+carry := by
  have hm := congrArg (fun n : ℕ => (n : ZMod (nsA R))) he
  have hg := normalizedGrid_mod P.M.base (nsReindex R) carry x' y'
  simp only [normalizedGrid,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] at hg
  have hr : gridResidue P.M.base (nsReindex R) x y+(nsB R : ZMod (nsA R))=
      gridResidue P.M.base (nsReindex R) x' y' := by
    simp only [Nat.cast_add,Nat.cast_mul] at hm
    simpa only [gridResidue,normalizedGrid,Nat.cast_add,Nat.cast_mul] using hm.trans hg
  refine ⟨hr,?_⟩
  have hs := (nonsymmetricPrefixIdeal R hQ).apery_step_eq (nsA R) (nsB R) (routingHB _ _)
    (gridResidue P.M.base (nsReindex R) x y)
  change nonsymmetricPrefixLambda R hQ _+nsB R=
    nonsymmetricPrefixLambda R hQ (_+(nsB R : ZMod (nsA R)))+
      nsA R*(nonsymmetricPrefixRouting R hQ).u _ at hs
  rw [hr,nonsymmetric_prefix_height_formula R hB hQ hd,
    nonsymmetric_prefix_height_formula R hB hQ hd'] at hs
  have heZ := congrArg (fun n : ℕ => (n : ℤ)) he
  simp only [Nat.cast_add,Nat.cast_mul] at heZ
  have ha : (0 : ℤ) < nsA R := by exact_mod_cast routingA_pos P.M.base (nsReindex R)
  have hu : ((nonsymmetricPrefixRouting R hQ).u (gridResidue P.M.base (nsReindex R) x y) : ℤ)+
      nonsymmetricPrefixDiagramHeight R hB hQ x' y'=
      nonsymmetricPrefixDiagramHeight R hB hQ x y+carry := by nlinarith only [hs,heZ,ha]
  exact_mod_cast hu

theorem nonsymmetric_prefix_c_edge (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {x y x' y' carry : ℕ}
    (hd : NonsymmetricLDomain R x y) (hd' : NonsymmetricLDomain R x' y')
    (he : x*nsB R+y*nsC R+nsC R=carry*nsA R+x'*nsB R+y'*nsC R) :
    (nonsymmetricPrefixRouting R hQ).c (gridResidue P.M.base (nsReindex R) x y)=
      gridResidue P.M.base (nsReindex R) x' y' ∧
    (nonsymmetricPrefixRouting R hQ).v (gridResidue P.M.base (nsReindex R) x y)+
      nonsymmetricPrefixDiagramHeight R hB hQ x' y'=
      nonsymmetricPrefixDiagramHeight R hB hQ x y+carry := by
  have hm := congrArg (fun n : ℕ => (n : ZMod (nsA R))) he
  have hg := normalizedGrid_mod P.M.base (nsReindex R) carry x' y'
  simp only [normalizedGrid,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] at hg
  have hr : gridResidue P.M.base (nsReindex R) x y+(nsC R : ZMod (nsA R))=
      gridResidue P.M.base (nsReindex R) x' y' := by
    simp only [Nat.cast_add,Nat.cast_mul] at hm
    simpa only [gridResidue,normalizedGrid,Nat.cast_add,Nat.cast_mul] using hm.trans hg
  refine ⟨hr,?_⟩
  have hs := (nonsymmetricPrefixIdeal R hQ).apery_step_eq (nsA R) (nsC R) (routingHC _ _)
    (gridResidue P.M.base (nsReindex R) x y)
  change nonsymmetricPrefixLambda R hQ _+nsC R=
    nonsymmetricPrefixLambda R hQ (_+(nsC R : ZMod (nsA R)))+
      nsA R*(nonsymmetricPrefixRouting R hQ).v _ at hs
  rw [hr,nonsymmetric_prefix_height_formula R hB hQ hd,
    nonsymmetric_prefix_height_formula R hB hQ hd'] at hs
  have heZ := congrArg (fun n : ℕ => (n : ℤ)) he
  simp only [Nat.cast_add,Nat.cast_mul] at heZ
  have ha : (0 : ℤ) < nsA R := by exact_mod_cast routingA_pos P.M.base (nsReindex R)
  have hv : ((nonsymmetricPrefixRouting R hQ).v (gridResidue P.M.base (nsReindex R) x y) : ℤ)+
      nonsymmetricPrefixDiagramHeight R hB hQ x' y'=
      nonsymmetricPrefixDiagramHeight R hB hQ x y+carry := by nlinarith only [hs,heZ,ha]
  exact_mod_cast hv

private theorem pred_mul {n g : ℕ} (hn : 0 < n) : (n-1)*g+g=n*g := by
  have he := congrArg (fun x => x*g) (Nat.sub_add_cancel (by omega : 1 ≤ n))
  simpa only [add_mul,one_mul] using he

theorem nonsymmetric_prefix_kappa1_carries (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    let D := nonsymmetricPrefixRouting R hQ
    D.u (nonsymmetricKappa1 R)=nonsymmetricDR R hB ∧
    D.v (nonsymmetricKappa1 R)=max (nonsymmetricDR R hB) (nonsymmetricDL0 R hB) ∧
    D.u (D.c (nonsymmetricKappa1 R))=0 ∧
    D.v (D.b (nonsymmetricKappa1 R))=
      max (nonsymmetricDR R hB) (nonsymmetricDL0 R hB)-nonsymmetricDR R hB := by
  have hp := nonsymmetric_coefficients R
  have rel := nonsymmetric_normalized_relations R
  have maxb := nonsymmetric_balanced_depth_maxima R hB hbal
  have bnd := nonsymmetric_boundary_depth_maxima_le R hB
  have hC2 : 0 < nsC2 R := by omega
  have hC3 : 0 < nsC3 R := by omega
  have pC2 := pred_mul (g:=nsB R) hC2
  have pC3 := pred_mul (g:=nsC R) hC3
  have pQ := pred_mul (g:=nsC R) hp.2.1
  have pZ := pred_mul (g:=nsB R) hp.2.2.2.2.2.1
  have s2 := congrArg (fun n => n*nsB R) hp.2.2.2.2.2.2.2.1
  have s3 := congrArg (fun n => n*nsC R) hp.2.2.2.2.2.2.2.2
  simp only [add_mul] at s2 s3
  have hd : NonsymmetricLDomain R (nsC2 R-1) (nsQ R-1) := ⟨by omega,by omega,Or.inr (by omega)⟩
  have hl : NonsymmetricLDomain R 0 (nsC3 R-1) := ⟨by omega,by omega,Or.inl hp.1⟩
  have hz : NonsymmetricLDomain R (nsZ R-1) 0 := ⟨by omega,by omega,Or.inr hp.2.1⟩
  have hz' : NonsymmetricLDomain R (nsZ R) 0 := ⟨by omega,by omega,Or.inr hp.2.1⟩
  have B := nonsymmetric_prefix_b_edge R hB hQ hd hl (carry:=nsU R) (by
    simp only [zero_mul,add_zero]; omega)
  have C := nonsymmetric_prefix_c_edge R hB hQ hd hz (carry:=nsC1 R) (by
    simp only [zero_mul,add_zero]; omega)
  have CB := nonsymmetric_prefix_b_edge R hB hQ hz hz' (carry:=0) (by
    simp only [zero_mul,add_zero,zero_add]; omega)
  have BC := nonsymmetric_prefix_c_edge R hB hQ hl hz' (carry:=nsW R) (by
    simp only [zero_mul,add_zero,zero_add]; omega)
  have h0 := nonsymmetric_prefix_corner1_height_zero R hB hQ hbal
  have ht := nonsymmetric_prefix_left_top_height R hB hQ hbal
  have hb0 := nonsymmetric_prefix_bottom_seam_height R hB hQ hbal (x:=nsZ R-1) (le_refl _) (by omega)
  have hb1 := nonsymmetric_prefix_bottom_seam_height R hB hQ hbal (x:=nsZ R) (by omega) (le_refl _)
  rw [h0,ht] at B
  rw [h0,hb0] at C
  rw [hb0,hb1] at CB
  rw [ht,hb1] at BC
  have B2 := B.2
  have C2 := C.2
  have CB2 := CB.2
  have BC2 := BC.2
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · change (nonsymmetricPrefixRouting R hQ).u (gridResidue P.M.base (nsReindex R) (nsC2 R-1) (nsQ R-1))=_
    omega
  · change (nonsymmetricPrefixRouting R hQ).v (gridResidue P.M.base (nsReindex R) (nsC2 R-1) (nsQ R-1))=_
    omega
  · rw [C.1]; omega
  · rw [B.1]; omega

theorem nonsymmetric_prefix_kappa2_carries (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    let D := nonsymmetricPrefixRouting R hQ
    D.v (nonsymmetricKappa2 R)=nonsymmetricDL R hB ∧
    D.u (nonsymmetricKappa2 R)=max (nonsymmetricDL R hB) (nonsymmetricDR0 R hB) ∧
    D.v (D.b (nonsymmetricKappa2 R))=0 ∧
    D.u (D.c (nonsymmetricKappa2 R))=
      max (nonsymmetricDL R hB) (nonsymmetricDR0 R hB)-nonsymmetricDL R hB := by
  have hp := nonsymmetric_coefficients R
  have rel := nonsymmetric_normalized_relations R
  have maxb := nonsymmetric_balanced_depth_maxima R hB hbal
  have bnd := nonsymmetric_boundary_depth_maxima_le R hB
  have hC2 : 0 < nsC2 R := by omega
  have hC3 : 0 < nsC3 R := by omega
  have pC2 := pred_mul (g:=nsB R) hC2
  have pC3 := pred_mul (g:=nsC R) hC3
  have pP := pred_mul (g:=nsB R) hp.1
  have pV := pred_mul (g:=nsC R) hp.2.2.2.1
  have s2 := congrArg (fun n => n*nsB R) hp.2.2.2.2.2.2.2.1
  have s3 := congrArg (fun n => n*nsC R) hp.2.2.2.2.2.2.2.2
  simp only [add_mul] at s2 s3
  have hd : NonsymmetricLDomain R (nsP R-1) (nsC3 R-1) := ⟨by omega,by omega,Or.inl (by omega)⟩
  have hb : NonsymmetricLDomain R (nsC2 R-1) 0 := ⟨by omega,by omega,Or.inr hp.2.1⟩
  have hv : NonsymmetricLDomain R 0 (nsV R-1) := ⟨by omega,by omega,Or.inl hp.1⟩
  have hv' : NonsymmetricLDomain R 0 (nsV R) := ⟨by omega,by omega,Or.inl hp.1⟩
  have C := nonsymmetric_prefix_c_edge R hB hQ hd hb (carry:=nsW R) (by
    simp only [zero_mul,add_zero]; omega)
  have B := nonsymmetric_prefix_b_edge R hB hQ hd hv (carry:=nsC1 R) (by
    simp only [zero_mul,add_zero,zero_add]; omega)
  have BC := nonsymmetric_prefix_c_edge R hB hQ hv hv' (carry:=0) (by
    simp only [zero_mul,add_zero,zero_add]; omega)
  have CB := nonsymmetric_prefix_b_edge R hB hQ hb hv' (carry:=nsU R) (by
    simp only [zero_mul,add_zero,zero_add]; omega)
  have h0 := nonsymmetric_prefix_corner2_height_zero R hB hQ hbal
  have ht := nonsymmetric_prefix_bottom_right_height R hB hQ hbal
  have hl0 := nonsymmetric_prefix_left_seam_height R hB hQ hbal (y:=nsV R-1) (le_refl _) (by omega)
  have hl1 := nonsymmetric_prefix_left_seam_height R hB hQ hbal (y:=nsV R) (by omega) (le_refl _)
  rw [h0,ht] at C
  rw [h0,hl0] at B
  rw [hl0,hl1] at BC
  rw [ht,hl1] at CB
  have C2 := C.2
  have B2 := B.2
  have BC2 := BC.2
  have CB2 := CB.2
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · change (nonsymmetricPrefixRouting R hQ).v (gridResidue P.M.base (nsReindex R) (nsP R-1) (nsC3 R-1))=_
    omega
  · change (nonsymmetricPrefixRouting R hQ).u (gridResidue P.M.base (nsReindex R) (nsP R-1) (nsC3 R-1))=_
    omega
  · rw [B.1]; omega
  · rw [C.1]; omega

theorem nonsymmetric_prefix_kappa1_unused_iff (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (nonsymmetricPrefixRouting R hQ)
      (nonsymmetricKappa1 R) ↔ nonsymmetricDL0 R hB ≤ nonsymmetricDR R hB := by
  have hc := nonsymmetric_prefix_kappa1_carries R hB hQ hbal
  have hp := nonsymmetric_balanced_depth_maxima R hB hbal
  unfold L5A2C4I.ResidueData.ExactUnusedMergeReverseBase
  rw [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  omega

theorem nonsymmetric_prefix_kappa2_unused_iff (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (nonsymmetricPrefixRouting R hQ)
      (nonsymmetricKappa2 R) ↔ nonsymmetricDR0 R hB ≤ nonsymmetricDL R hB := by
  have hc := nonsymmetric_prefix_kappa2_carries R hB hQ hbal
  have hp := nonsymmetric_balanced_depth_maxima R hB hbal
  unfold L5A2C4I.ResidueData.ExactUnusedMergeReverseBase
  rw [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  omega

def nonsymmetric_prefix_kappa1_fakeSeat (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R)
      (routingHB _ _) (routingHC _ _) := by
  refine ⟨nonsymmetricKappa1 R,?_,?_⟩
  · change (nonsymmetricPrefixRouting R hQ).u (nonsymmetricKappa1 R) ≠ 0 ∧
      (nonsymmetricPrefixRouting R hQ).v (nonsymmetricKappa1 R) ≠ 0
    have hc := nonsymmetric_prefix_kappa1_carries R hB hQ hbal
    have hp := nonsymmetric_balanced_depth_maxima R hB hbal
    rw [hc.1,hc.2.1]; omega
  · change nonsymmetricPrefixLambda R hQ _-nsA R ∉ (nsH R).asRelativeIdeal
    have hp := nonsymmetric_coefficients R
    have hd : NonsymmetricLDomain R (nsC2 R-1) (nsQ R-1) := ⟨by omega,by omega,Or.inr (by omega)⟩
    rw [nonsymmetric_prefix_height_formula R hB hQ hd,
      nonsymmetric_prefix_corner1_height_zero R hB hQ hbal,Nat.cast_zero,zero_mul,zero_add]
    simpa only [Nat.cast_add,Nat.cast_mul] using nonsymmetric_canonical_a_predecessor_not_mem R hd

def nonsymmetric_prefix_kappa2_fakeSeat (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R)
      (routingHB _ _) (routingHC _ _) := by
  refine ⟨nonsymmetricKappa2 R,?_,?_⟩
  · change (nonsymmetricPrefixRouting R hQ).u (nonsymmetricKappa2 R) ≠ 0 ∧
      (nonsymmetricPrefixRouting R hQ).v (nonsymmetricKappa2 R) ≠ 0
    have hc := nonsymmetric_prefix_kappa2_carries R hB hQ hbal
    have hp := nonsymmetric_balanced_depth_maxima R hB hbal
    rw [hc.1,hc.2.1]; omega
  · change nonsymmetricPrefixLambda R hQ _-nsA R ∉ (nsH R).asRelativeIdeal
    have hp := nonsymmetric_coefficients R
    have hd : NonsymmetricLDomain R (nsP R-1) (nsC3 R-1) := ⟨by omega,by omega,Or.inl (by omega)⟩
    rw [nonsymmetric_prefix_height_formula R hB hQ hd,
      nonsymmetric_prefix_corner2_height_zero R hB hQ hbal,Nat.cast_zero,zero_mul,zero_add]
    simpa only [Nat.cast_add,Nat.cast_mul] using nonsymmetric_canonical_a_predecessor_not_mem R hd

theorem nonsymmetric_lShape_grid_injective (R : SectorBCriticalRoleBranchB P)
    {x y x' y' : ℕ} (hd : NonsymmetricLDomain R x y) (hd' : NonsymmetricLDomain R x' y')
    (he : gridResidue P.M.base (nsReindex R) x y=gridResidue P.M.base (nsReindex R) x' y') :
    x=x' ∧ y=y' := by
  have dom {i j : ℕ} (hi : NonsymmetricLDomain R i j) :
      L5A2C4OR5.HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) i j := by
    simpa only [NonsymmetricLDomain,L5A2C4OR5.HerzogLShapeDomain,
      branchB_inactive_coherent_c2,branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12,branchB_inactive_coherent_cr13] using hi
  have hc := L5A2C4OR6.herzogLShapeCanonicality P.M.base (nsReindex R)
    (branchB_inactive_coherentHerzogData R) x y (dom hd)
  have hc' := L5A2C4OR6.herzogLShapeCanonicality P.M.base (nsReindex R)
    (branchB_inactive_coherentHerzogData R) x' y' (dom hd')
  change normalizedGrid P.M.base (nsReindex R) 0 x y=
    physicalAlpha P.M.base (nsReindex R) (gridResidue P.M.base (nsReindex R) x y) at hc
  change normalizedGrid P.M.base (nsReindex R) 0 x' y'=
    physicalAlpha P.M.base (nsReindex R) (gridResidue P.M.base (nsReindex R) x' y') at hc'
  rw [he] at hc
  have hv := hc.trans hc'.symm
  simp only [normalizedGrid,zero_mul,zero_add] at hv
  have hvNat : 0*nsA R+x*nsB R+y*nsC R=0*nsA R+x'*nsB R+y'*nsC R := by
    have hn : x*nsB R+y*nsC R=x'*nsB R+y'*nsC R := by
      exact_mod_cast (show ((x*nsB R+y*nsC R : ℕ) : ℤ)=((x'*nsB R+y'*nsC R : ℕ) : ℤ) from hv)
    simpa only [zero_mul,zero_add] using hn
  exact (nonsymmetric_lShape_degree_injective R hd hd' hvNat).2

theorem nonsymmetric_prefix_corners_distinct (R : SectorBCriticalRoleBranchB P) :
    nonsymmetricKappa1 R ≠ nonsymmetricKappa2 R := by
  intro he
  have hp := nonsymmetric_coefficients R
  have hd : NonsymmetricLDomain R (nsC2 R-1) (nsQ R-1) := ⟨by omega,by omega,Or.inr (by omega)⟩
  have hd' : NonsymmetricLDomain R (nsP R-1) (nsC3 R-1) := ⟨by omega,by omega,Or.inl (by omega)⟩
  have hc := nonsymmetric_lShape_grid_injective R hd hd' he
  omega

def nonsymmetricPrefixCorner (R : SectorBCriticalRoleBranchB P) (b : Bool) : ZMod (nsA R) :=
  if b then nonsymmetricKappa1 R else nonsymmetricKappa2 R

def NonsymmetricCornerUnusedTags (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  {b : Bool // L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (nonsymmetricPrefixRouting R hQ)
    (nonsymmetricPrefixCorner R b)}

theorem nonsymmetric_corner_unused_tag_count (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    Nat.card (NonsymmetricCornerUnusedTags R hQ)=nonsymmetricFU R hB := by
  unfold NonsymmetricCornerUnusedTags
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [Fintype.univ_bool,Finset.sum_insert,Finset.mem_singleton,Bool.true_eq_false,
    not_false_eq_true,Finset.sum_singleton]
  change (if L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (nonsymmetricPrefixRouting R hQ)
      (nonsymmetricKappa1 R) then 1 else 0)+
    (if L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (nonsymmetricPrefixRouting R hQ)
      (nonsymmetricKappa2 R) then 1 else 0)=_
  rw [nonsymmetric_prefix_kappa1_unused_iff R hB hQ hbal,
    nonsymmetric_prefix_kappa2_unused_iff R hB hQ hbal]
  unfold nonsymmetricFU
  split_ifs <;> rfl

def nonsymmetricCornerUnusedResource (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (b : NonsymmetricCornerUnusedTags R hQ) :
    L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ) :=
  ⟨nonsymmetricPrefixCorner R b.val,b.property⟩

theorem nonsymmetricCornerUnusedResource_injective (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricCornerUnusedResource R hQ) := by
  intro x y he
  have hv := congrArg Subtype.val he
  apply Subtype.ext
  change nonsymmetricPrefixCorner R x.val=nonsymmetricPrefixCorner R y.val at hv
  cases hx : x.val <;> cases hy : y.val
  · rfl
  · have hf := nonsymmetric_prefix_corners_distinct R
    simp only [nonsymmetricPrefixCorner,hx,hy,Bool.false_eq_true,ite_false,ite_true] at hv
    exact (hf hv.symm).elim
  · have hf := nonsymmetric_prefix_corners_distinct R
    simp only [nonsymmetricPrefixCorner,hx,hy,Bool.false_eq_true,ite_false,ite_true] at hv
    exact (hf hv).elim
  · rfl

theorem nonsymmetric_prefix_unused_count_ge_FU (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    nonsymmetricFU R hB ≤
      Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ)) := by
  letI : Finite (L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ)) := Subtype.finite
  rw [← nonsymmetric_corner_unused_tag_count R hB hQ hbal]
  exact Nat.card_le_card_of_injective _ (nonsymmetricCornerUnusedResource_injective R hQ)

def nonsymmetricCornerFakeResource (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) (b : Bool) :
    FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R)
      (routingHB _ _) (routingHC _ _) :=
  if b then nonsymmetric_prefix_kappa1_fakeSeat R hB hQ hbal
    else nonsymmetric_prefix_kappa2_fakeSeat R hB hQ hbal

theorem nonsymmetricCornerFakeResource_injective (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    Function.Injective (nonsymmetricCornerFakeResource R hB hQ hbal) := by
  intro x y he
  have hv := congrArg Subtype.val he
  cases x <;> cases y
  · rfl
  · exact (nonsymmetric_prefix_corners_distinct R hv.symm).elim
  · exact (nonsymmetric_prefix_corners_distinct R hv).elim
  · rfl

theorem nonsymmetric_prefix_fake_count_ge_two (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    2 ≤ Nat.card (FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R)
      (routingHB _ _) (routingHC _ _)) := by
  letI : Finite (FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R)
    (routingHB _ _) (routingHC _ _)) := Subtype.finite
  have he := Nat.card_le_card_of_injective _ (nonsymmetricCornerFakeResource_injective R hB hQ hbal)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_bool] using he

end NS25Lean.L5A2BFinalRepair
