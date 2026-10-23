import NS25Lean.P2BranchBHalfPlaneSlack

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}
local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

private theorem final_Q_one (R : SectorBCriticalRoleBranchB P)
    (hQ : actualPrincipalIndex P.M.base=1) (z : ℤ) :
    z ∈ routingI P.M.base (nsReindex R) ↔ z-normalizedM P.M.base ∈ (nsH R).asRelativeIdeal := by
  rw [mem_normalizedTailIdeal_iff_positive_return (chosenBase_minimalFour P.M.base (nsReindex R))]
  change z ∈ positiveReturnCarrier (nsH R) (normalizedM P.M.base) ↔ _
  rw [positiveReturnCarrier_eq_finalCarrier (nsH R) (normalizedM P.M.base) P.M.base.q_positive]
  have he : principalIndex (nsH R) (normalizedM P.M.base) P.M.base.q_positive=actualPrincipalIndex P.M.base := by
    rw [nonsymmetric_H_eq_normalizedH R]
  rw [he,hQ,mem_finalCarrier_iff]
  simp only [Nat.cast_one,one_mul,mem_prefixCarrier_iff]
  constructor
  · rintro (⟨ell,hp,hl,_⟩ | hz)
    · omega
    · exact hz
  · exact Or.inr

theorem nonsymmetric_Q_one_impossible (R : SectorBCriticalRoleBranchB P)
    (hQ : actualPrincipalIndex P.M.base=1) : False := by
  have coeff := nonsymmetric_coefficients R
  have floor := branchB_inactive_H0_lt R
  change eta P.M.base (nsReindex R) 0 0 < nsC1 R at floor
  have hm : (((nsC1 R-1)*nsA R : ℕ) : ℤ) ∈ routingI P.M.base (nsReindex R) := by
    have hh := (normalizedGrid_mem_iff_eta_le P.M.base (nsReindex R) (nsC1 R-1) 0 0).mpr (by omega)
    simpa only [normalizedGrid,zero_mul,add_zero] using hh
  have div := (final_Q_one R hQ _).mp hm
  have mf : normalizedM P.M.base ∈ nsH R := by
    have hs := (nonsymmetricPrincipalDegree R).property
    change actualPrincipalIndex P.M.base * normalizedM P.M.base ∈ nsH R at hs
    simpa only [hQ,one_mul] using hs
  obtain ⟨w,hw,he⟩ := div
  obtain ⟨a,b,c,hfac⟩ := L5A2C4OR6.routingH_factorization P.M.base (nsReindex R) mf
  obtain ⟨a',b',c',hwfac⟩ := L5A2C4OR6.routingH_factorization P.M.base (nsReindex R) hw
  change normalizedM P.M.base=a*nsA R+b*nsB R+c*nsC R at hfac
  change w=a'*nsA R+b'*nsB R+c'*nsC R at hwfac
  have eqn : (nsC1 R-1)*nsA R=(a+a')*nsA R+(b+b')*nsB R+(c+c')*nsC R := by
    have eqnN : (nsC1 R-1)*nsA R=normalizedM P.M.base+w := by
      exact_mod_cast (show (((nsC1 R-1)*nsA R : ℕ) : ℤ)=normalizedM P.M.base+(w : ℤ) by omega)
    rw [eqnN,hfac,hwfac]
    ring
  have hc := nonsymmetric_subcritical_a_factorization R (by omega) eqn
  have hb0 : b=0 := by omega
  have hc0 : c=0 := by omega
  have hpure : normalizedM P.M.base=a*nsA R := by simpa only [hb0,hc0,zero_mul,add_zero] using hfac
  have ap : 0 < a := by
    have mp := P.M.base.q_positive
    change 0 < normalizedM P.M.base at mp
    by_contra hn
    have hz : a=0 := by omega
    rw [hz,zero_mul] at hpure
    omega
  have seam (x y : ℕ) (hd : NonsymmetricLDomain R x y)
      (hz : eta P.M.base (nsReindex R) x y=0) : False := by
    have hm := (normalizedGrid_mem_iff_eta_le P.M.base (nsReindex R) 0 x y).mpr (by omega)
    have hzmem : (((x*nsB R+y*nsC R : ℕ) : ℤ)-normalizedM P.M.base) ∈ (nsH R).asRelativeIdeal :=
      (final_Q_one R hQ _).mp (by simpa only [normalizedGrid,zero_mul,zero_add] using hm)
    obtain ⟨t,ht,hte⟩ := nonsymmetric_grid_mem R (a-1) 0 0
    have hadd := (nsH R).asRelativeIdeal.add_mem hzmem ht
    apply nonsymmetric_canonical_a_predecessor_not_mem R hd
    have ha : ((a-1 : ℕ) : ℤ)+1=a := by omega
    have hpureZ : (normalizedM P.M.base : ℤ)=(a : ℤ)*nsA R := by exact_mod_cast hpure
    simp only [zero_mul,add_zero,Nat.cast_mul] at hte
    have hval : ((x*nsB R+y*nsC R : ℕ) : ℤ)-nsA R=
        ((x*nsB R+y*nsC R : ℕ) : ℤ)-normalizedM P.M.base+(t : ℤ) := by
      nlinarith only [ha,hpureZ,hte]
    rw [hval]
    exact hadd
  rcases branchB_inactive_seam_zero R with hz | hz
  · apply seam (nsP R-1) (nsQ R) (by unfold NonsymmetricLDomain; omega)
    exact hz
  · apply seam (nsP R) (nsQ R-1) (by unfold NonsymmetricLDomain; omega)
    exact hz

theorem nonsymmetric_actual_type_le_sourceCount (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) : Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  have hp := nonsymmetric_Q_positive R
  have hn : actualPrincipalIndex P.M.base ≠ 1 := fun h => nonsymmetric_Q_one_impossible R h
  exact nonsymmetric_Q_gt_one_actual_type_le_sourceCount R hB (by omega)

theorem nonsymmetric_not_entry (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) : P.W ≠ 1 := by
  have h := nonsymmetric_actual_type_le_sourceCount R hB
  rw [P2Data.W]
  omega

theorem sectorB_actual_type_le_sourceCount (P : P2Data Gamma) (hB : SectorB P.M) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  rcases sectorB_criticalRole_dichotomy P hB with hA | hR
  · obtain ⟨A⟩ := hA
    exact symmetric_actual_type_le_sourceCount A hB
  · obtain ⟨R⟩ := hR
    exact nonsymmetric_actual_type_le_sourceCount R hB

theorem sectorB_not_entry (P : P2Data Gamma) (hB : SectorB P.M) : P.W ≠ 1 := by
  have h := sectorB_actual_type_le_sourceCount P hB
  rw [P2Data.W]
  omega

end NS25Lean.L5A2BFinalRepair
