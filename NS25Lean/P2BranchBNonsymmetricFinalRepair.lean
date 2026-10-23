import NS25Lean.P2BranchBSymmetricSmallQ
import NS25Lean.P2BranchBHighAxisBEndpointClamp

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2BFinalRepair

open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
open ToricPresentation

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-! All coordinates below are in the inactive chart, not the old selected-anchor chart. -/

abbrev nsReindex (R : SectorBCriticalRoleBranchB P) := branchBInactiveReindex R
abbrev nsA (R : SectorBCriticalRoleBranchB P) := routingA P.M.base (nsReindex R)
abbrev nsB (R : SectorBCriticalRoleBranchB P) := routingB P.M.base (nsReindex R)
abbrev nsC (R : SectorBCriticalRoleBranchB P) := routingC P.M.base (nsReindex R)
abbrev nsH (R : SectorBCriticalRoleBranchB P) := routingH P.M.base (nsReindex R)
abbrev nsC1 (R : SectorBCriticalRoleBranchB P) := L5A2B4AR4R2B.c3 R
abbrev nsC2 (R : SectorBCriticalRoleBranchB P) := L5A2B4AR4R2B.c1 R
abbrev nsC3 (R : SectorBCriticalRoleBranchB P) := L5A2B4AR4R2B.c2 R
abbrev nsP (R : SectorBCriticalRoleBranchB P) := L5A2B4AR4R2B.r31 R
abbrev nsQ (R : SectorBCriticalRoleBranchB P) := L5A2B4AR4R2B.r32 R
abbrev nsU (R : SectorBCriticalRoleBranchB P) := L5A2B4AR4R2B.r13 R
abbrev nsV (R : SectorBCriticalRoleBranchB P) := L5A2B4AR4R2B.r12 R
abbrev nsW (R : SectorBCriticalRoleBranchB P) := L5A2B4AR4R2B.r23 R
abbrev nsZ (R : SectorBCriticalRoleBranchB P) := L5A2B4AR4R2B.r21 R

def NonsymmetricLDomain (R : SectorBCriticalRoleBranchB P) (i j : ℕ) : Prop :=
  i < nsC2 R ∧ j < nsC3 R ∧ (i < nsP R ∨ j < nsQ R)

theorem nonsymmetric_coefficients (R : SectorBCriticalRoleBranchB P) :
    0 < nsP R ∧ 0 < nsQ R ∧ 0 < nsU R ∧ 0 < nsV R ∧
      0 < nsW R ∧ 0 < nsZ R ∧
      nsC1 R = nsU R + nsW R ∧ nsC2 R = nsP R + nsZ R ∧
      nsC3 R = nsQ R + nsV R := by
  have hp := L5A2C4D.coherent_coefficients_positive P.M.base (nsReindex R)
    (branchB_inactive_coherentHerzogData R)
  have hs := L5A2C4D.coherent_coefficients P.M.base (nsReindex R)
    (branchB_inactive_coherentHerzogData R)
  have hpack := And.intro hp.1 (And.intro hp.2.1 (And.intro hp.2.2.1
    (And.intro hp.2.2.2.1 (And.intro hp.2.2.2.2.1
      (And.intro hp.2.2.2.2.2 hs)))))
  simpa only [nsReindex, branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13,
    branchB_inactive_coherent_cr21, branchB_inactive_coherent_cr23,
    branchB_inactive_coherent_cr31, branchB_inactive_coherent_cr32,
    branchB_inactive_coherent_c1, branchB_inactive_coherent_c2,
    branchB_inactive_coherent_c3] using
    hpack

theorem nonsymmetric_normalized_relations (R : SectorBCriticalRoleBranchB P) :
    nsC1 R * nsA R = nsP R * nsB R + nsQ R * nsC R ∧
      nsC2 R * nsB R = nsU R * nsA R + nsV R * nsC R ∧
      nsC3 R * nsC R = nsW R * nsA R + nsZ R * nsB R := by
  simpa only [nsReindex, branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13,
    branchB_inactive_coherent_cr21, branchB_inactive_coherent_cr23,
    branchB_inactive_coherent_cr31, branchB_inactive_coherent_cr32,
    branchB_inactive_coherent_c1, branchB_inactive_coherent_c2,
    branchB_inactive_coherent_c3] using
    L5A2C4OR5.coherent_normalized_relations P.M.base (nsReindex R)
      (branchB_inactive_coherentHerzogData R)

theorem nonsymmetric_grid_mem (R : SectorBCriticalRoleBranchB P) (t i j : ℕ) :
    ((t * nsA R + i * nsB R + j * nsC R : ℕ) : ℤ) ∈ (nsH R).asRelativeIdeal := by
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
  refine ⟨_, ?_, rfl⟩
  exact (mem_generatedThree_iff _ _ _ _).mpr ⟨t,i,j,rfl⟩

theorem nonsymmetric_returnIdeal_le_final (R : SectorBCriticalRoleBranchB P)
    {ell : ℕ} (hp : 0 < ell) {s : ℤ}
    (hs : s ∈ returnIdeal (nsH R) (ell * normalizedM P.M.base)) :
    s ∈ routingI P.M.base (nsReindex R) := by
  exact (mem_normalizedTailIdeal_iff_positive_return
    (chosenBase_minimalFour P.M.base (nsReindex R)) s).mpr ⟨ell,hp,hs⟩

theorem nonsymmetric_live_pure_predecessors (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) :
    (((nsC2 R-1)*nsB R : ℕ) : ℤ) ∉ routingI P.M.base (nsReindex R) ∧
      (((nsC3 R-1)*nsC R : ℕ) : ℤ) ∉ routingI P.M.base (nsReindex R) := by
  constructor
  · intro hz
    have hm := (normalizedGrid_mem_iff_eta_le P.M.base (nsReindex R) 0 (nsC2 R-1) 0).mp
      (by simpa only [normalizedGrid,zero_mul,zero_add,add_zero] using hz)
    have hp := branchB_inactive_first_pure_height_pos R hB
    change eta P.M.base (nsReindex R) (nsC2 R-1) 0 > 0 at hp
    omega
  · intro hz
    have hm := (normalizedGrid_mem_iff_eta_le P.M.base (nsReindex R) 0 0 (nsC3 R-1)).mp
      (by simpa only [normalizedGrid,zero_mul,zero_add] using hz)
    have hp := branchB_inactive_second_pure_height_pos R hB
    change eta P.M.base (nsReindex R) 0 (nsC3 R-1) > 0 at hp
    omega

private theorem ns_nat_mem_of_int_mem {H : NumericalSemigroup} {n : ℕ}
    (hn : (n : ℤ) ∈ H.asRelativeIdeal) : n ∈ H := by
  obtain ⟨u,hu,he⟩ := hn
  have he' : n=u := by exact_mod_cast he
  exact he' ▸ hu

private theorem ns_axis_not_mem_return (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell t : ℕ} (hp : 0 < ell) :
    (t < nsC2 R → ((t*nsB R : ℕ) : ℤ) ∉ returnIdeal (nsH R) (ell*normalizedM P.M.base)) ∧
      (t < nsC3 R → ((t*nsC R : ℕ) : ℤ) ∉ returnIdeal (nsH R) (ell*normalizedM P.M.base)) := by
  have he := nonsymmetric_live_pure_predecessors R hB
  constructor
  · intro ht hz
    have hd := ns_nat_mem_of_int_mem (nonsymmetric_grid_mem R 0 (nsC2 R-1-t) 0)
    simp only [zero_mul,zero_add,add_zero] at hd
    have hm := (routingI P.M.base (nsReindex R)).add_mem
      (nonsymmetric_returnIdeal_le_final R hp hz) hd
    have hs : (t*nsB R : ℤ)+((nsC2 R-1-t)*nsB R : ℕ)=((nsC2 R-1)*nsB R : ℕ) := by
      have h : t+(nsC2 R-1-t)=nsC2 R-1 := by omega
      exact_mod_cast (show t*nsB R+(nsC2 R-1-t)*nsB R=(nsC2 R-1)*nsB R by rw [← add_mul,h])
    exact he.1 (hs ▸ hm)
  · intro ht hz
    have hd := ns_nat_mem_of_int_mem (nonsymmetric_grid_mem R 0 0 (nsC3 R-1-t))
    simp only [zero_mul,zero_add] at hd
    have hm := (routingI P.M.base (nsReindex R)).add_mem
      (nonsymmetric_returnIdeal_le_final R hp hz) hd
    have hs : (t*nsC R : ℤ)+((nsC3 R-1-t)*nsC R : ℕ)=((nsC3 R-1)*nsC R : ℕ) := by
      have h : t+(nsC3 R-1-t)=nsC3 R-1 := by omega
      exact_mod_cast (show t*nsC R+(nsC3 R-1-t)*nsC R=(nsC3 R-1)*nsC R by rw [← add_mul,h])
    exact he.2 (hs ▸ hm)

/-- Actual inactive-chart admission. The depth bounds are conclusions from LIVE,
not fields or hypotheses of a strict-arm parameter packet. -/
theorem nonsymmetric_single_return_admission (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell i j depth : ℕ} (hp : 0 < ell)
    (hdom : NonsymmetricLDomain R i j)
    (hb : i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R) :
    0 < i ∧ 0 < j ∧ (i < nsP R → depth < nsW R) ∧
      (j < nsQ R → depth < nsU R) := by
  let n := ell*normalizedM P.M.base
  have hF : ((i*nsB R+j*nsC R : ℕ) : ℤ) ∈ returnIdeal (nsH R) n := by
    refine ⟨by simpa only [zero_mul,zero_add] using nonsymmetric_grid_mem R 0 i j, ?_⟩
    change ((i*nsB R+j*nsC R : ℕ) : ℤ)-(n : ℕ) ∈ (nsH R).asRelativeIdeal
    have he : ((i*nsB R+j*nsC R : ℕ) : ℤ)-(n : ℕ)=(depth*nsA R : ℕ) := by
      have hbZ : ((i*nsB R+j*nsC R : ℕ) : ℤ)=(n : ℕ)+(depth*nsA R : ℕ) := by exact_mod_cast hb
      omega
    rw [he]
    simpa only [zero_mul,add_zero] using nonsymmetric_grid_mem R depth 0 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hn
    have hz : i=0 := by omega
    exact (ns_axis_not_mem_return R hB hp).2 hdom.2.1 (by simpa [hz,n] using hF)
  · by_contra hn
    have hz : j=0 := by omega
    exact (ns_axis_not_mem_return R hB hp).1 hdom.1 (by simpa [hz,n] using hF)
  · intro hi
    by_contra hn
    have hd : nsW R ≤ depth := by omega
    have hs := nonsymmetric_coefficients R
    have ht : i+nsZ R < nsC2 R := by omega
    apply (ns_axis_not_mem_return R hB hp).1 ht
    refine ⟨by simpa only [zero_mul,zero_add,add_zero] using nonsymmetric_grid_mem R 0 (i+nsZ R) 0, ?_⟩
    change (((i+nsZ R)*nsB R : ℕ) : ℤ)-(n : ℕ) ∈ (nsH R).asRelativeIdeal
    have he : (((i+nsZ R)*nsB R : ℕ) : ℤ)-(n : ℕ)=
        ((depth-nsW R)*nsA R+(nsC3 R-j)*nsC R : ℕ) := by
      have hr := (nonsymmetric_normalized_relations R).2.2
      have hd' := Nat.sub_add_cancel hd
      have hj' := Nat.sub_add_cancel (le_of_lt hdom.2.1)
      have hbZ : (i : ℤ)*nsB R+j*nsC R=(n : ℕ)+(depth : ℤ)*nsA R := by exact_mod_cast hb
      have hrZ : (nsC3 R : ℤ)*nsC R=nsW R*nsA R+nsZ R*nsB R := by exact_mod_cast hr
      have hdZ : (depth-nsW R : ℕ)+(nsW R : ℤ)=depth := by exact_mod_cast hd'
      have hjZ : (nsC3 R-j : ℕ)+(j : ℤ)=nsC3 R := by exact_mod_cast hj'
      simp only [Nat.cast_add,Nat.cast_mul]
      nlinarith only [hbZ,hrZ,hdZ,hjZ]
    rw [he]
    simpa only [zero_mul,add_zero] using nonsymmetric_grid_mem R (depth-nsW R) 0 (nsC3 R-j)
  · intro hj
    by_contra hn
    have hd : nsU R ≤ depth := by omega
    have hs := nonsymmetric_coefficients R
    have ht : j+nsV R < nsC3 R := by omega
    apply (ns_axis_not_mem_return R hB hp).2 ht
    refine ⟨by simpa only [zero_mul,zero_add] using nonsymmetric_grid_mem R 0 0 (j+nsV R), ?_⟩
    change (((j+nsV R)*nsC R : ℕ) : ℤ)-(n : ℕ) ∈ (nsH R).asRelativeIdeal
    have he : (((j+nsV R)*nsC R : ℕ) : ℤ)-(n : ℕ)=
        ((depth-nsU R)*nsA R+(nsC2 R-i)*nsB R : ℕ) := by
      have hr := (nonsymmetric_normalized_relations R).2.1
      have hd' := Nat.sub_add_cancel hd
      have hi' := Nat.sub_add_cancel (le_of_lt hdom.1)
      have hbZ : (i : ℤ)*nsB R+j*nsC R=(n : ℕ)+(depth : ℤ)*nsA R := by exact_mod_cast hb
      have hrZ : (nsC2 R : ℤ)*nsB R=nsU R*nsA R+nsV R*nsC R := by exact_mod_cast hr
      have hdZ : (depth-nsU R : ℕ)+(nsU R : ℤ)=depth := by exact_mod_cast hd'
      have hiZ : (nsC2 R-i : ℕ)+(i : ℤ)=nsC2 R := by exact_mod_cast hi'
      simp only [Nat.cast_add,Nat.cast_mul]
      nlinarith only [hbZ,hrZ,hdZ,hiZ]
    rw [he]
    simpa only [zero_mul,add_zero] using nonsymmetric_grid_mem R (depth-nsU R) (nsC2 R-i) 0

theorem nonsymmetric_signed_height_mem_iff (R : SectorBCriticalRoleBranchB P)
    {i j : ℕ} (hdom : NonsymmetricLDomain R i j) (height : ℤ) :
    height*nsA R+i*nsB R+j*nsC R ∈ (nsH R).asRelativeIdeal ↔ 0 ≤ height := by
  let B := P.M.base
  let e := nsReindex R
  letI : NeZero (routingA B e) := ⟨(routingA_pos B e).ne'⟩
  have ha : (0 : ℤ) < nsA R := by exact_mod_cast routingA_pos B e
  have hd : L5A2C4OR5.HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) i j := by
    simpa only [NonsymmetricLDomain,L5A2C4OR5.HerzogLShapeDomain,branchB_inactive_coherent_c2,
      branchB_inactive_coherent_c3,branchB_inactive_coherent_cr12,
      branchB_inactive_coherent_cr13] using hdom
  have hc := L5A2C4OR6.herzogLShapeCanonicality B e
    (branchB_inactive_coherentHerzogData R) i j hd
  have hc' : physicalAlpha B e (gridResidue B e i j)=(i : ℤ)*nsB R+j*nsC R := by
    rw [← hc]
    simp only [normalizedGrid,zero_mul,zero_add,Nat.cast_add,Nat.cast_mul]
    rfl
  constructor
  · intro hz
    have hmod : ((height*nsA R+i*nsB R+j*nsC R : ℤ) : ZMod (routingA B e))=
        gridResidue B e i j := by
      simp only [gridResidue,Int.cast_add,Int.cast_mul,Int.cast_natCast]
      change (height : ZMod (routingA B e))*(routingA B e : ZMod (routingA B e))+
        (i : ZMod (routingA B e))*routingB B e+
        (j : ZMod (routingA B e))*routingC B e=_
      simp only [ZMod.natCast_self,mul_zero,zero_add]
    have hle := (nsH R).asRelativeIdeal.aperyRepresentative_le
      (routingA B e) (gridResidue B e i j) hz hmod
    change physicalAlpha B e (gridResidue B e i j) ≤ _ at hle
    rw [hc'] at hle
    nlinarith
  · intro hh
    have he : height=(height.toNat : ℕ) := (Int.toNat_of_nonneg hh).symm
    rw [he]
    simpa only [Nat.cast_add,Nat.cast_mul] using nonsymmetric_grid_mem R height.toNat i j

/-- Every actual preprincipal level has an inactive-chart canonical return.
No source/anchor identification and no owner selector enter this theorem. -/
theorem nonsymmetric_nonprincipal_return_packet (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell : ℕ} (hp : 0 < ell)
    (hl : ell < actualPrincipalIndex P.M.base) :
    ∃ i j depth : ℕ, NonsymmetricLDomain R i j ∧ 0 < i ∧ 0 < j ∧
      0 < depth ∧ (i < nsP R → depth < nsW R) ∧
      (j < nsQ R → depth < nsU R) ∧
      i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R := by
  let B := P.M.base
  let a := nsA R
  let H := nsH R
  let n := ell*normalizedM B
  letI : NeZero a := ⟨(routingA_pos B (nsReindex R)).ne'⟩
  let beta := H.asRelativeIdeal.aperyRepresentative a (n : ZMod a)
  have hn : n ∉ H := by
    change ell*normalizedM B ∉ routingH B (branchBInactiveReindex R)
    rw [branchBRoutingH_eq_normalizedH R]
    intro hm
    exact (Nat.not_le_of_gt hl) (principalIndex_min _ _ B.q_positive hp hm)
  have hbmem : beta ∈ H.asRelativeIdeal := H.asRelativeIdeal.aperyRepresentative_mem a _
  have hbmod : (beta : ZMod a)=((n : ℤ) : ZMod a) := by
    simpa only [Int.cast_natCast] using H.asRelativeIdeal.aperyRepresentative_mod a (n : ZMod a)
  have haH : a ∈ H := ns_nat_mem_of_int_mem
    (by simpa only [one_mul,zero_mul,add_zero] using nonsymmetric_grid_mem R 1 0 0)
  have hnlt : (n : ℤ) < beta := by
    by_contra hnot
    obtain ⟨k,hk⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq a (by omega) hbmod.symm
    have hm := H.asRelativeIdeal.add_mem hbmem
      (show a*k ∈ H from by simpa [nsmul_eq_mul,mul_comm] using H.toAddSubmonoid.nsmul_mem haH k)
    have hm' : (n : ℤ) ∈ H.asRelativeIdeal := by rw [hk]; exact hm
    exact hn (ns_nat_mem_of_int_mem hm')
  obtain ⟨depth,hd⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq a (le_of_lt hnlt) hbmod
  have hdp : 0 < depth := by
    by_contra hn
    have hzero : depth=0 := by omega
    simp only [hzero,Nat.cast_zero,mul_zero,add_zero] at hd
    omega
  obtain ⟨i,j,hdom,_hres,hcanon⟩ :=
    branchB_physicalAlpha_canonical_coordinates R (n : ZMod a)
  have hd' : NonsymmetricLDomain R i j := by
    simpa only [NonsymmetricLDomain,L5A2C4OR5.HerzogLShapeDomain,branchB_inactive_coherent_c2,
      branchB_inactive_coherent_c3,branchB_inactive_coherent_cr12,
      branchB_inactive_coherent_cr13] using hdom
  have he : i*nsB R+j*nsC R=ell*normalizedM B+depth*nsA R := by
    have hc : beta=((normalizedGrid B (nsReindex R) 0 i j : ℕ) : ℤ) := hcanon
    have heZ := hc.symm.trans hd
    simp only [normalizedGrid,zero_mul,zero_add,Nat.cast_add,Nat.cast_mul] at heZ
    have heN : i*routingB B (nsReindex R)+j*routingC B (nsReindex R)=n+a*depth := by
      exact_mod_cast heZ
    simpa only [n,a,mul_comm] using heN
  have had := nonsymmetric_single_return_admission R hB hp hd' he
  exact ⟨i,j,depth,hd',had.1,had.2.1,hdp,had.2.2.1,had.2.2.2,he⟩

/-- Exact K1 first-carry criterion, before specializing to CENTER/RB/LT.
The right side is a derived threshold, not assumed family completeness. -/
theorem nonsymmetric_single_return_colon_threshold (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell i j depth x y height : ℕ} (hp : 0 < ell)
    (hij : NonsymmetricLDomain R i j)
    (hb : i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R) :
    ((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)+(ell*normalizedM P.M.base : ℕ) ∈
        (nsH R).asRelativeIdeal ↔
      depth ≤ height ∨ nsC2 R ≤ x+i ∨ nsC3 R ≤ y+j ∨
        (nsP R ≤ x+i ∧ nsQ R ≤ y+j) := by
  have had := nonsymmetric_single_return_admission R hB hp hij hb
  have hs := nonsymmetric_coefficients R
  have hr := nonsymmetric_normalized_relations R
  have hdc1 : depth < nsC1 R := by
    rcases hij.2.2 with hi | hj
    · have hd := had.2.2.1 hi
      omega
    · have hd := had.2.2.2 hj
      omega
  have hbZ : (i : ℤ)*nsB R+j*nsC R=
      (ell*normalizedM P.M.base : ℕ)+(depth : ℤ)*nsA R := by exact_mod_cast hb
  simp only [Nat.cast_mul] at hbZ
  constructor
  · intro hm
    by_contra hn
    push Not at hn
    have hd' : NonsymmetricLDomain R (x+i) (y+j) :=
      ⟨hn.2.1,hn.2.2.1,by omega⟩
    have he : ((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)+
        (ell*normalizedM P.M.base : ℕ)=
        ((height : ℤ)-depth)*nsA R+(x+i)*nsB R+(y+j)*nsC R := by
      simp only [Nat.cast_add,Nat.cast_mul]
      nlinarith only [hbZ]
    rw [he] at hm
    have hd := (nonsymmetric_signed_height_mem_iff R hd' ((height : ℤ)-depth)).mp hm
    omega
  · intro hh
    by_cases hd : depth ≤ height
    · have hdZ : ((height-depth : ℕ) : ℤ)+depth=height := by
        exact_mod_cast Nat.sub_add_cancel hd
      have he : ((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)+
          (ell*normalizedM P.M.base : ℕ)=
          (( (height-depth)*nsA R+(x+i)*nsB R+(y+j)*nsC R : ℕ) : ℤ) := by
        simp only [Nat.cast_add,Nat.cast_mul]
        nlinarith only [hbZ,hdZ]
      rw [he]
      exact nonsymmetric_grid_mem R (height-depth) (x+i) (y+j)
    by_cases hin : nsP R ≤ x+i ∧ nsQ R ≤ y+j
    · have hc : depth ≤ height+nsC1 R := by omega
      have hdZ : ((height+nsC1 R-depth : ℕ) : ℤ)+depth=height+nsC1 R := by
        exact_mod_cast Nat.sub_add_cancel hc
      have hxZ : ((x+i-nsP R : ℕ) : ℤ)+nsP R=x+i := by
        exact_mod_cast Nat.sub_add_cancel hin.1
      have hyZ : ((y+j-nsQ R : ℕ) : ℤ)+nsQ R=y+j := by
        exact_mod_cast Nat.sub_add_cancel hin.2
      have hrZ : (nsC1 R : ℤ)*nsA R=nsP R*nsB R+nsQ R*nsC R := by exact_mod_cast hr.1
      have he : ((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)+
          (ell*normalizedM P.M.base : ℕ)=
          (((height+nsC1 R-depth)*nsA R+(x+i-nsP R)*nsB R+
            (y+j-nsQ R)*nsC R : ℕ) : ℤ) := by
        simp only [Nat.cast_add,Nat.cast_mul]
        nlinarith only [hbZ,hdZ,hxZ,hyZ,hrZ]
      rw [he]
      exact nonsymmetric_grid_mem R (height+nsC1 R-depth) (x+i-nsP R) (y+j-nsQ R)
    rcases hh with hh | hh | hh | hh
    · exact (hd hh).elim
    · have hj : j < nsQ R := by omega
      have hdu := had.2.2.2 hj
      have hc : depth ≤ height+nsU R := by omega
      have hdZ : ((height+nsU R-depth : ℕ) : ℤ)+depth=height+nsU R := by
        exact_mod_cast Nat.sub_add_cancel hc
      have hxZ : ((x+i-nsC2 R : ℕ) : ℤ)+nsC2 R=x+i := by
        exact_mod_cast Nat.sub_add_cancel hh
      have hrZ : (nsC2 R : ℤ)*nsB R=nsU R*nsA R+nsV R*nsC R := by exact_mod_cast hr.2.1
      have he : ((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)+
          (ell*normalizedM P.M.base : ℕ)=
          (((height+nsU R-depth)*nsA R+(x+i-nsC2 R)*nsB R+
            (y+j+nsV R)*nsC R : ℕ) : ℤ) := by
        simp only [Nat.cast_add,Nat.cast_mul]
        nlinarith only [hbZ,hdZ,hxZ,hrZ]
      rw [he]
      exact nonsymmetric_grid_mem R (height+nsU R-depth) (x+i-nsC2 R) (y+j+nsV R)
    · have hi : i < nsP R := by omega
      have hdw := had.2.2.1 hi
      have hc : depth ≤ height+nsW R := by omega
      have hdZ : ((height+nsW R-depth : ℕ) : ℤ)+depth=height+nsW R := by
        exact_mod_cast Nat.sub_add_cancel hc
      have hyZ : ((y+j-nsC3 R : ℕ) : ℤ)+nsC3 R=y+j := by
        exact_mod_cast Nat.sub_add_cancel hh
      have hrZ : (nsC3 R : ℤ)*nsC R=nsW R*nsA R+nsZ R*nsB R := by exact_mod_cast hr.2.2
      have he : ((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)+
          (ell*normalizedM P.M.base : ℕ)=
          (((height+nsW R-depth)*nsA R+(x+i+nsZ R)*nsB R+
            (y+j-nsC3 R)*nsC R : ℕ) : ℤ) := by
        simp only [Nat.cast_add,Nat.cast_mul]
        nlinarith only [hbZ,hdZ,hyZ,hrZ]
      rw [he]
      exact nonsymmetric_grid_mem R (height+nsW R-depth) (x+i+nsZ R) (y+j-nsC3 R)
    · exact (hin hh).elim

theorem nonsymmetric_center_colon_threshold (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell i j depth x y height : ℕ} (hp : 0 < ell)
    (hij : NonsymmetricLDomain R i j) (hxy : NonsymmetricLDomain R x y)
    (hi : i < nsP R) (hj : j < nsQ R)
    (hb : i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R) :
    ((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)+(ell*normalizedM P.M.base : ℕ) ∈
      (nsH R).asRelativeIdeal ↔ depth ≤ height ∨ nsC2 R-i ≤ x ∨ nsC3 R-j ≤ y ∨
        (nsP R-i ≤ x ∧ nsQ R-j ≤ y) := by
  rw [nonsymmetric_single_return_colon_threshold R hB hp hij hb]
  omega

theorem nonsymmetric_RB_colon_threshold (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell i j depth x y height : ℕ} (hp : 0 < ell)
    (hij : NonsymmetricLDomain R i j) (hxy : NonsymmetricLDomain R x y)
    (hi : nsP R ≤ i) (hj : j < nsQ R)
    (hb : i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R) :
    ((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)+(ell*normalizedM P.M.base : ℕ) ∈
      (nsH R).asRelativeIdeal ↔ depth ≤ height ∨ nsC2 R-i ≤ x ∨ nsQ R-j ≤ y := by
  rw [nonsymmetric_single_return_colon_threshold R hB hp hij hb]
  have hs := nonsymmetric_coefficients R
  omega

theorem nonsymmetric_LT_colon_threshold (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {ell i j depth x y height : ℕ} (hp : 0 < ell)
    (hij : NonsymmetricLDomain R i j) (hxy : NonsymmetricLDomain R x y)
    (hi : i < nsP R) (hj : nsQ R ≤ j)
    (hb : i*nsB R+j*nsC R=ell*normalizedM P.M.base+depth*nsA R) :
    ((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)+(ell*normalizedM P.M.base : ℕ) ∈
      (nsH R).asRelativeIdeal ↔ depth ≤ height ∨ nsP R-i ≤ x ∨ nsC3 R-j ≤ y := by
  rw [nonsymmetric_single_return_colon_threshold R hB hp hij hb]
  have hs := nonsymmetric_coefficients R
  omega

abbrev NonsymmetricReturnIndex (R : SectorBCriticalRoleBranchB P) :=
  {ell : ℕ // 0 < ell ∧ ell < actualPrincipalIndex P.M.base}

private theorem nonsymmetric_tuple_exists (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (ell : NonsymmetricReturnIndex R) :
    ∃ t : ℕ×ℕ×ℕ, NonsymmetricLDomain R t.1 t.2.1 ∧ 0 < t.1 ∧ 0 < t.2.1 ∧
      0 < t.2.2 ∧ (t.1 < nsP R → t.2.2 < nsW R) ∧
      (t.2.1 < nsQ R → t.2.2 < nsU R) ∧
      t.1*nsB R+t.2.1*nsC R=ell.val*normalizedM P.M.base+t.2.2*nsA R := by
  obtain ⟨i,j,depth,h⟩ := nonsymmetric_nonprincipal_return_packet R hB ell.property.1 ell.property.2
  exact ⟨(i,j,depth),h⟩

def nonsymmetricReturnTuple (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (ell : NonsymmetricReturnIndex R) : ℕ×ℕ×ℕ :=
  Classical.choose (nonsymmetric_tuple_exists R hB ell)

theorem nonsymmetricReturnTuple_spec (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (ell : NonsymmetricReturnIndex R) :
    let t := nonsymmetricReturnTuple R hB ell
    NonsymmetricLDomain R t.1 t.2.1 ∧ 0 < t.1 ∧ 0 < t.2.1 ∧
      0 < t.2.2 ∧ (t.1 < nsP R → t.2.2 < nsW R) ∧
      (t.2.1 < nsQ R → t.2.2 < nsU R) ∧
      t.1*nsB R+t.2.1*nsC R=ell.val*normalizedM P.M.base+t.2.2*nsA R :=
  Classical.choose_spec (nonsymmetric_tuple_exists R hB ell)

theorem nonsymmetricReturnNonempty (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Nonempty (NonsymmetricReturnIndex R) :=
  ⟨⟨1,by omega,hQ⟩⟩

abbrev nonsymmetricDa (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  natMinImage (nonsymmetricReturnNonempty R hQ) (fun ell => (nonsymmetricReturnTuple R hB ell).2.2)

theorem nonsymmetricDa_positive (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) : 0 < nonsymmetricDa R hB hQ := by
  obtain ⟨ell,he⟩ := natMinImage_spec (nonsymmetricReturnNonempty R hQ)
    (fun ell => (nonsymmetricReturnTuple R hB ell).2.2)
  change 0 < natMinImage _ _
  rw [← he]
  exact (nonsymmetricReturnTuple_spec R hB ell).2.2.2.1

theorem nonsymmetric_colon_coordinates (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {height x y : ℕ} :
    ((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ) ∈
      principalColonCarrier (nsH R) (normalizedM P.M.base) (actualPrincipalIndex P.M.base) ↔
    ∃ ell : NonsymmetricReturnIndex R,
      let t := nonsymmetricReturnTuple R hB ell
      t.2.2 ≤ height ∨ nsC2 R ≤ x+t.1 ∨ nsC3 R ≤ y+t.2.1 ∨
        (nsP R ≤ x+t.1 ∧ nsQ R ≤ y+t.2.1) := by
  have hf : actualPrincipalIndex P.M.base*normalizedM P.M.base ∈ nsH R := by
    change _ ∈ routingH P.M.base (branchBInactiveReindex R)
    rw [branchBRoutingH_eq_normalizedH R]
    exact (actualPrincipalIndex_spec P.M.base).2
  rw [principal_colon_cyclic_reverse _ _ _ hf]
  have hsingle (ell : NonsymmetricReturnIndex R) :=
    nonsymmetric_single_return_colon_threshold R hB (height:=height) (x:=x) (y:=y) ell.property.1
      (nonsymmetricReturnTuple_spec R hB ell).1
      (nonsymmetricReturnTuple_spec R hB ell).2.2.2.2.2.2
  constructor
  · rintro ⟨_,ell,hp,hl,hm⟩
    exact ⟨⟨ell,hp,hl⟩,(hsingle ⟨ell,hp,hl⟩).mp hm⟩
  · rintro ⟨ell,hh⟩
    exact ⟨nonsymmetric_grid_mem R height x y,ell.val,ell.property.1,ell.property.2,
      (hsingle ell).mpr hh⟩

/-- The balanced condition is an actual case predicate on return coordinates,
not a stored depth/rank/slack conclusion. Common-half-plane data are separate. -/
def NonsymmetricBalancedReturns (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) : Prop :=
  (∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).1 < nsP R) ∧
    (∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R)

theorem nonsymmetric_balanced_min_depth (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    nonsymmetricDa R hB hQ < nsU R ∧ nonsymmetricDa R hB hQ < nsW R := by
  obtain ⟨⟨l,hl⟩,⟨r,hr⟩⟩ := hbal
  constructor
  · exact lt_of_le_of_lt (natMinImage_le _ _ r) ((nonsymmetricReturnTuple_spec R hB r).2.2.2.2.2.1 hr)
  · exact lt_of_le_of_lt (natMinImage_le _ _ l) ((nonsymmetricReturnTuple_spec R hB l).2.2.2.2.1 hl)

def nonsymmetricPrefixIdeal (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) : RelativeIdeal (nsH R) :=
  principalPrefixIdeal (nsH R) (normalizedM P.M.base) (actualPrincipalIndex P.M.base) hQ

def nonsymmetricPrincipalDegree (R : SectorBCriticalRoleBranchB P) : (nsH R).toAddSubmonoid :=
  ⟨actualPrincipalIndex P.M.base*normalizedM P.M.base,by
    change _ ∈ routingH P.M.base (branchBInactiveReindex R)
    rw [branchBRoutingH_eq_normalizedH R]
    exact (actualPrincipalIndex_spec P.M.base).2⟩

def nonsymmetricPrincipalColonIdeal (k : Type*) [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Ideal (SemigroupAlgebra k (nsH R).toAddSubmonoid) :=
  (carrierMonomialIdeal k (nonsymmetricPrefixIdeal R hQ)).colon
    {AddMonoidAlgebra.single (nonsymmetricPrincipalDegree R) (1 : k)}

abbrev nonsymmetricPrincipalColonQuotient (k : Type*) [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  SemigroupAlgebra k (nsH R).toAddSubmonoid ⧸ nonsymmetricPrincipalColonIdeal k R hQ

theorem nonsymmetric_principal_colon_single_mem_iff {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base)
    (h : (nsH R).toAddSubmonoid) :
    AddMonoidAlgebra.single h (1 : k) ∈ nonsymmetricPrincipalColonIdeal k R hQ ↔
      (h.val : ℤ) ∈ principalColonCarrier (nsH R) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base) := by
  rw [nonsymmetricPrincipalColonIdeal,carrierMonomialIdeal_colon_mem_iff]
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.support_single _ one_ne_zero,
    Finset.mem_singleton,forall_eq]
  change ((actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) : ℤ)+h.val ∈
    prefixCarrier (nsH R) (normalizedM P.M.base) (actualPrincipalIndex P.M.base) ↔ _
  exact (and_iff_right (show (h.val : ℤ) ∈ (nsH R).asRelativeIdeal from ⟨h.val,h.property,rfl⟩)).symm

theorem nonsymmetric_principal_colon_grid_mem_iff {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (h : (nsH R).toAddSubmonoid)
    {height x y : ℕ}
    (he : h.val=height*nsA R+x*nsB R+y*nsC R) :
    AddMonoidAlgebra.single h (1 : k) ∈ nonsymmetricPrincipalColonIdeal k R hQ ↔
      ∃ ell : NonsymmetricReturnIndex R,
        let t := nonsymmetricReturnTuple R hB ell
        t.2.2 ≤ height ∨ nsC2 R ≤ x+t.1 ∨ nsC3 R ≤ y+t.2.1 ∨
          (nsP R ≤ x+t.1 ∧ nsQ R ≤ y+t.2.1) := by
  rw [nonsymmetric_principal_colon_single_mem_iff,he]
  exact nonsymmetric_colon_coordinates R hB

def nonsymmetricGridDegree (R : SectorBCriticalRoleBranchB P) (height x y : ℕ) :
    (nsH R).toAddSubmonoid :=
  ⟨height*nsA R+x*nsB R+y*nsC R,
    ns_nat_mem_of_int_mem (nonsymmetric_grid_mem R height x y)⟩

def nonsymmetricTailMonomialDegree (R : SectorBCriticalRoleBranchB P) (i : Fin 3) :
    (nsH R).toAddSubmonoid :=
  ⟨![nsA R,nsB R,nsC R] i,by
    fin_cases i
    · exact ns_nat_mem_of_int_mem (by simpa using nonsymmetric_grid_mem R 1 0 0)
    · exact ns_nat_mem_of_int_mem (by simpa using nonsymmetric_grid_mem R 0 1 0)
    · exact ns_nat_mem_of_int_mem (by simpa using nonsymmetric_grid_mem R 0 0 1)⟩

def nonsymmetricColonPolynomialMap {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    MvPolynomial (Fin 3) k →ₐ[k] nonsymmetricPrincipalColonQuotient k R hQ :=
  MvPolynomial.aeval (fun i => Ideal.Quotient.mkₐ k (nonsymmetricPrincipalColonIdeal k R hQ)
    (AddMonoidAlgebra.single (nonsymmetricTailMonomialDegree R i) 1))

/-- The actual E2 staircase presentation; arm thresholds automatically degenerate
to a pure endpoint. No bound on the number of mixed corners is assumed. -/
def nonsymmetricPolynomialColonIdeal (k : Type*) [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ({MvPolynomial.X 0 ^ nonsymmetricDa R hB hQ} ∪
    Set.range (fun lt : NonsymmetricReturnIndex R × Fin 3 =>
      let t := nonsymmetricReturnTuple R hB lt.1
      ![MvPolynomial.X 1 ^ (nsC2 R-t.1),
        MvPolynomial.X 2 ^ (nsC3 R-t.2.1),
        MvPolynomial.X 1 ^ (nsP R-t.1)*MvPolynomial.X 2 ^ (nsQ R-t.2.1)] lt.2))

open MvPolynomial

theorem nonsymmetricColonPolynomialMap_Xpow {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base)
    (i : Fin 3) (d : ℕ) :
    nonsymmetricColonPolynomialMap (k:=k) R hQ (X i ^ d)=
      Ideal.Quotient.mkₐ k (nonsymmetricPrincipalColonIdeal k R hQ)
        (AddMonoidAlgebra.single (d • nonsymmetricTailMonomialDegree R i) 1) := by
  rw [map_pow]
  simp only [nonsymmetricColonPolynomialMap,aeval_X]
  rw [← map_pow,AddMonoidAlgebra.single_pow,one_pow]

theorem nonsymmetricColonPolynomialMap_xyz {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base)
    (height x y : ℕ) :
    nonsymmetricColonPolynomialMap (k:=k) R hQ (X 0 ^ height*X 1 ^ x*X 2 ^ y)=
      Ideal.Quotient.mkₐ k (nonsymmetricPrincipalColonIdeal k R hQ)
        (AddMonoidAlgebra.single (nonsymmetricGridDegree R height x y) 1) := by
  rw [map_mul,map_mul,nonsymmetricColonPolynomialMap_Xpow,
    nonsymmetricColonPolynomialMap_Xpow,nonsymmetricColonPolynomialMap_Xpow,
    ← map_mul,← map_mul,AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.single_mul_single]
  have he : height • nonsymmetricTailMonomialDegree R 0+x • nonsymmetricTailMonomialDegree R 1+
      y • nonsymmetricTailMonomialDegree R 2=nonsymmetricGridDegree R height x y := by
    apply Subtype.ext
    simp [nonsymmetricGridDegree,nonsymmetricTailMonomialDegree]
  rw [he]
  simp

theorem nonsymmetricColonPolynomialMap_surjective {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Surjective (nonsymmetricColonPolynomialMap (k:=k) R hQ) := by
  intro z
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective z
  change ∃ p, nonsymmetricColonPolynomialMap (k:=k) R hQ p=
    Ideal.Quotient.mkₐ k (nonsymmetricPrincipalColonIdeal k R hQ) f
  induction f using AddMonoidAlgebra.induction_on with
  | of h =>
    obtain ⟨height,x,y,he⟩ := L5A2C4OR6.routingH_factorization P.M.base (nsReindex R) h.property
    refine ⟨X 0 ^ height*X 1 ^ x*X 2 ^ y,?_⟩
    rw [nonsymmetricColonPolynomialMap_xyz]
    congr 2
    exact Subtype.ext he.symm
  | add f g hf hg =>
    obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
    exact ⟨p+q,by rw [map_add,hp,hq,map_add]⟩
  | smul a f hf =>
    obtain ⟨p,hp⟩ := hf
    exact ⟨a • p,by rw [map_smul,hp,map_smul]⟩

theorem nonsymmetric_polynomial_colon_le_eval_kernel {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPolynomialColonIdeal k R hB hQ ≤
      RingHom.ker (nonsymmetricColonPolynomialMap (k:=k) R hQ).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f (hf | hf)
  · rcases hf with rfl
    change nonsymmetricColonPolynomialMap (k:=k) R hQ (X 0 ^ nonsymmetricDa R hB hQ)=0
    rw [nonsymmetricColonPolynomialMap_Xpow,Ideal.Quotient.mkₐ_eq_mk,Ideal.Quotient.eq_zero_iff_mem]
    apply (nonsymmetric_principal_colon_grid_mem_iff R hB hQ _
      (height:=nonsymmetricDa R hB hQ) (x:=0) (y:=0) (by
        simp [nonsymmetricTailMonomialDegree])).mpr
    obtain ⟨ell,he⟩ := natMinImage_spec (nonsymmetricReturnNonempty R hQ)
      (fun ell => (nonsymmetricReturnTuple R hB ell).2.2)
    exact ⟨ell,Or.inl (by simpa [nonsymmetricDa] using le_of_eq he)⟩
  · obtain ⟨⟨ell,i⟩,rfl⟩ := hf
    have ht := nonsymmetricReturnTuple_spec R hB ell
    fin_cases i
    · change nonsymmetricColonPolynomialMap (k:=k) R hQ
        (X 1 ^ (nsC2 R-(nonsymmetricReturnTuple R hB ell).1))=0
      rw [nonsymmetricColonPolynomialMap_Xpow,Ideal.Quotient.mkₐ_eq_mk,Ideal.Quotient.eq_zero_iff_mem]
      apply (nonsymmetric_principal_colon_grid_mem_iff R hB hQ _ (height:=0)
        (x:=nsC2 R-(nonsymmetricReturnTuple R hB ell).1) (y:=0)
        (by simp [nonsymmetricTailMonomialDegree])).mpr
      exact ⟨ell,Or.inr (Or.inl (by have := ht.1.1; omega))⟩
    · change nonsymmetricColonPolynomialMap (k:=k) R hQ
        (X 2 ^ (nsC3 R-(nonsymmetricReturnTuple R hB ell).2.1))=0
      rw [nonsymmetricColonPolynomialMap_Xpow,Ideal.Quotient.mkₐ_eq_mk,Ideal.Quotient.eq_zero_iff_mem]
      apply (nonsymmetric_principal_colon_grid_mem_iff R hB hQ _ (height:=0)
        (x:=0) (y:=nsC3 R-(nonsymmetricReturnTuple R hB ell).2.1)
        (by simp [nonsymmetricTailMonomialDegree])).mpr
      exact ⟨ell,Or.inr (Or.inr (Or.inl (by have := ht.1.2.1; omega)))⟩
    · change nonsymmetricColonPolynomialMap (k:=k) R hQ
        (X 1 ^ (nsP R-(nonsymmetricReturnTuple R hB ell).1)*
          X 2 ^ (nsQ R-(nonsymmetricReturnTuple R hB ell).2.1))=0
      have hm := nonsymmetricColonPolynomialMap_xyz (k:=k) R hQ 0
        (nsP R-(nonsymmetricReturnTuple R hB ell).1)
        (nsQ R-(nonsymmetricReturnTuple R hB ell).2.1)
      simp only [pow_zero,one_mul] at hm
      rw [hm,Ideal.Quotient.mkₐ_eq_mk,Ideal.Quotient.eq_zero_iff_mem]
      apply (nonsymmetric_principal_colon_grid_mem_iff R hB hQ _ rfl).mpr
      exact ⟨ell,Or.inr (Or.inr (Or.inr (by constructor <;> omega)))⟩

def nonsymmetricColonFactor {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    (MvPolynomial (Fin 3) k ⧸ nonsymmetricPolynomialColonIdeal k R hB hQ) →ₐ[k]
      nonsymmetricPrincipalColonQuotient k R hQ :=
  Ideal.Quotient.liftₐ _ (nonsymmetricColonPolynomialMap R hQ)
    (fun _ hp => nonsymmetric_polynomial_colon_le_eval_kernel R hB hQ hp)

theorem nonsymmetricColonFactor_surjective {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Surjective (nonsymmetricColonFactor (k:=k) R hB hQ) := by
  intro y
  obtain ⟨p,hp⟩ := nonsymmetricColonPolynomialMap_surjective (k:=k) R hQ y
  exact ⟨Ideal.Quotient.mk _ p,hp⟩

def nonsymmetricColonExponentSet (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Set (Fin 3 →₀ ℕ) :=
  {Finsupp.single 0 (nonsymmetricDa R hB hQ)} ∪
    Set.range (fun lt : NonsymmetricReturnIndex R × Fin 3 =>
      let t := nonsymmetricReturnTuple R hB lt.1
      ![Finsupp.single 1 (nsC2 R-t.1),
        Finsupp.single 2 (nsC3 R-t.2.1),
        Finsupp.single 1 (nsP R-t.1)+Finsupp.single 2 (nsQ R-t.2.1)] lt.2)

theorem nonsymmetric_polynomial_colon_monomial_presentation {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPolynomialColonIdeal k R hB hQ =
      Ideal.span ((fun a => monomial a (1 : k)) '' nonsymmetricColonExponentSet R hB hQ) := by
  unfold nonsymmetricPolynomialColonIdeal
  congr 1
  rw [nonsymmetricColonExponentSet,Set.image_union,Set.image_singleton,← Set.range_comp]
  congr 1
  · simp [X_pow_eq_monomial]
  · congr 1
    funext lt
    rcases lt with ⟨ell,i⟩
    fin_cases i <;> simp [Function.comp_def,X_pow_eq_monomial,monomial_mul]

theorem nonsymmetric_polynomial_colon_isMonomial {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    L2B.IsMonomialIdeal k (nonsymmetricPolynomialColonIdeal k R hB hQ) :=
  ⟨nonsymmetricColonExponentSet R hB hQ,nonsymmetric_polynomial_colon_monomial_presentation R hB hQ⟩

theorem nonsymmetric_polynomial_colon_monomial_mem {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (a : Fin 3 →₀ ℕ) :
    monomial a (1 : k) ∈ nonsymmetricPolynomialColonIdeal k R hB hQ ↔
      nonsymmetricDa R hB hQ ≤ a 0 ∨
      ∃ ell : NonsymmetricReturnIndex R,
        let t := nonsymmetricReturnTuple R hB ell
        nsC2 R ≤ a 1+t.1 ∨ nsC3 R ≤ a 2+t.2.1 ∨
          (nsP R ≤ a 1+t.1 ∧ nsQ R ≤ a 2+t.2.1) := by
  rw [nonsymmetric_polynomial_colon_monomial_presentation,L3A.monomial_mem_span_iff]
  constructor
  · rintro ⟨_,hf,ha⟩
    rcases hf with hf | hf
    · rcases hf with rfl
      exact Or.inl (by simpa using ha 0)
    · obtain ⟨⟨ell,i⟩,rfl⟩ := hf
      right; refine ⟨ell,?_⟩
      have ht := nonsymmetricReturnTuple_spec R hB ell
      fin_cases i
      · left; have h1 := ha 1
        have := ht.1.1
        simp at *; omega
      · right; left; have h2 := ha 2
        have := ht.1.2.1
        simp at *; omega
      · right; right; have h1 := ha 1; have h2 := ha 2
        simp at *; constructor <;> omega
  · rintro (hh | ⟨ell,hh⟩)
    · refine ⟨_,Or.inl rfl,?_⟩
      intro i; fin_cases i <;> simp [hh]
    · rcases hh with hh | hh | hh
      · refine ⟨_,Or.inr ⟨(ell,0),rfl⟩,?_⟩
        intro i; fin_cases i <;> simp at * <;> omega
      · refine ⟨_,Or.inr ⟨(ell,1),rfl⟩,?_⟩
        intro i; fin_cases i <;> simp at * <;> omega
      · refine ⟨_,Or.inr ⟨(ell,2),rfl⟩,?_⟩
        intro i; fin_cases i <;> simp at * <;> omega

theorem nonsymmetric_standard_domain {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (a : L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ)) :
    a.val 0 < nonsymmetricDa R hB hQ ∧ NonsymmetricLDomain R (a.val 1) (a.val 2) := by
  have hn := a.property
  change monomial a.val (1 : k) ∉ nonsymmetricPolynomialColonIdeal k R hB hQ at hn
  rw [nonsymmetric_polynomial_colon_monomial_mem] at hn
  have ha : a.val 0 < nonsymmetricDa R hB hQ := by
    by_contra hh; exact hn (Or.inl (by omega))
  let ell : NonsymmetricReturnIndex R := ⟨1,by omega,hQ⟩
  have hcx : a.val 1 < nsC2 R := by
    by_contra hh
    exact hn (Or.inr ⟨ell,Or.inl (by omega)⟩)
  have hcy : a.val 2 < nsC3 R := by
    by_contra hh
    exact hn (Or.inr ⟨ell,Or.inr (Or.inl (by omega))⟩)
  have hc : a.val 1 < nsP R ∨ a.val 2 < nsQ R := by
    by_contra hh
    push Not at hh
    exact hn (Or.inr ⟨ell,Or.inr (Or.inr (by constructor <;> omega))⟩)
  exact ⟨ha,hcx,hcy,hc⟩

theorem nonsymmetric_standard_actual_survives {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (a : L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ)) :
    AddMonoidAlgebra.single (nonsymmetricGridDegree R (a.val 0) (a.val 1) (a.val 2)) (1 : k)
      ∉ nonsymmetricPrincipalColonIdeal k R hQ := by
  intro hm
  obtain ⟨ell,hh⟩ := (nonsymmetric_principal_colon_grid_mem_iff R hB hQ _ rfl).mp hm
  apply a.property
  apply (nonsymmetric_polynomial_colon_monomial_mem R hB hQ a.val).mpr
  rcases hh with hh | hh | hh | hh
  · left; exact le_trans (natMinImage_le _ _ ell) hh
  · exact Or.inr ⟨ell,Or.inl hh⟩
  · exact Or.inr ⟨ell,Or.inr (Or.inl hh)⟩
  · exact Or.inr ⟨ell,Or.inr (Or.inr hh)⟩

theorem nonsymmetric_lShape_degree_injective (R : SectorBCriticalRoleBranchB P)
    {h i j h' i' j' : ℕ} (hd : NonsymmetricLDomain R i j)
    (hd' : NonsymmetricLDomain R i' j')
    (he : h*nsA R+i*nsB R+j*nsC R=h'*nsA R+i'*nsB R+j'*nsC R) :
    h=h' ∧ i=i' ∧ j=j' := by
  let D := branchB_inactive_coherentHerzogData R
  have shape {x y : ℕ} (hx : NonsymmetricLDomain R x y) :
      L5A2B.InLShape (L5A2C4D.cr12 D) (L5A2C4D.cr13 D)
        (L5A2C4D.cr32 D) (L5A2C4D.cr23 D) x y := by
    rcases nonsymmetric_coefficients R with ⟨_,_,_,_,_,_,_,hs2,hs3⟩
    have hx' : L5A2B.InLShape (nsP R) (nsQ R) (nsZ R) (nsV R) x y := by
      unfold L5A2B.InLShape
      refine ⟨by positivity,by positivity,?_,?_,?_⟩
      · have hh : x < nsP R+nsZ R := hs2 ▸ hx.1
        exact_mod_cast hh
      · have hh : y < nsQ R+nsV R := hs3 ▸ hx.2.1
        exact_mod_cast hh
      · exact_mod_cast hx.2.2
    simpa only [D,branchB_inactive_coherent_cr12,branchB_inactive_coherent_cr13,
      branchB_inactive_coherent_cr32,branchB_inactive_coherent_cr23] using hx'
  have heZ : (h : ℤ)*nsA R+i*nsB R+j*nsC R=
      (h' : ℤ)*nsA R+i'*nsB R+j'*nsC R := by exact_mod_cast he
  have hm : Int.ModEq (nsA R) ((i' : ℤ)*nsB R+j'*nsC R)
      ((i : ℤ)*nsB R+j*nsC R) := by
    change _ % (nsA R : ℤ)=_ % (nsA R : ℤ)
    have hh := congrArg (fun z : ℤ => z % nsA R) heZ
    simpa only [Int.add_emod,Int.mul_emod,Int.emod_self,mul_zero,Int.zero_emod,
      zero_add,Int.emod_emod] using hh.symm
  obtain ⟨ij,_,hu⟩ := L5A2C4OR6.coherent_lShape_unique_coordinate P.M.base (nsReindex R) D
    ((i : ℤ)*nsB R+j*nsC R)
  have hi := hu ((i : ℤ),(j : ℤ)) ⟨shape hd,Int.ModEq.refl _⟩
  have hj := hu ((i' : ℤ),(j' : ℤ)) ⟨shape hd',hm⟩
  have hh := hi.trans hj.symm
  have hii : i=i' := by
    have hx := congrArg Prod.fst hh
    dsimp only at hx
    exact_mod_cast hx
  have hjj : j=j' := by
    have hx := congrArg Prod.snd hh
    dsimp only at hx
    exact_mod_cast hx
  have ha := routingA_pos P.M.base (nsReindex R)
  rw [hii,hjj] at he
  exact ⟨by nlinarith,hii,hjj⟩

theorem nonsymmetric_principal_colon_eq_translated_carrier {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPrincipalColonIdeal k R hQ = carrierMonomialIdeal k
      ((nonsymmetricPrefixIdeal R hQ).translate
        (-((actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) : ℤ))) := by
  ext p
  rw [nonsymmetricPrincipalColonIdeal,carrierMonomialIdeal_colon_mem_iff,carrierMonomialIdeal_mem_iff]
  simp only [RelativeIdeal.mem_translate_iff,sub_neg_eq_add,AddSubmonoid.coe_add,
    Nat.cast_add,nonsymmetricPrincipalDegree,add_comm]

def nonsymmetricStandardSurvivor {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (a : L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ)) :
    CarrierSurvivingDegrees ((nonsymmetricPrefixIdeal R hQ).translate
      (-((actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) : ℤ))) :=
  ⟨nonsymmetricGridDegree R (a.val 0) (a.val 1) (a.val 2),by
    have hn := nonsymmetric_standard_actual_survives R hB hQ a
    rw [nonsymmetric_principal_colon_eq_translated_carrier,carrierMonomialIdeal_mem_iff] at hn
    simpa using hn⟩

theorem nonsymmetricStandardSurvivor_injective {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricStandardSurvivor (k:=k) R hB hQ) := by
  intro a b he
  have hn := congrArg (fun z => z.val.val) he
  obtain ⟨h0,h1,h2⟩ := nonsymmetric_lShape_degree_injective R
    (nonsymmetric_standard_domain R hB hQ a).2 (nonsymmetric_standard_domain R hB hQ b).2 hn
  apply Subtype.ext
  ext i
  fin_cases i <;> assumption

theorem nonsymmetricColonPolynomialMap_monomial {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base)
    (a : Fin 3 →₀ ℕ) :
    nonsymmetricColonPolynomialMap (k:=k) R hQ (monomial a 1)=
      Ideal.Quotient.mkₐ k (nonsymmetricPrincipalColonIdeal k R hQ)
        (AddMonoidAlgebra.single (nonsymmetricGridDegree R (a 0) (a 1) (a 2)) 1) := by
  have he : a=symmetricBoxExponent (a 0) (a 1) (a 2) := by
    ext i; fin_cases i <;> simp [symmetricBoxExponent]
  have hm : monomial a (1 : k)=X 0 ^ (a 0)*X 1 ^ (a 1)*X 2 ^ (a 2) := by
    conv_lhs => rw [he]
    simp [symmetricBoxExponent,X_pow_eq_monomial,monomial_mul]
  rw [hm,nonsymmetricColonPolynomialMap_xyz]

theorem nonsymmetricColonFactor_standard_independent {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearIndependent k (fun a : L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ) =>
      nonsymmetricColonFactor (k:=k) R hB hQ (L3A.monomialClass _ a.val)) := by
  have hi := (carrierMonomial_linearIndependent (k:=k)
      ((nonsymmetricPrefixIdeal R hQ).translate
        (-((actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) : ℤ)))).comp
      (nonsymmetricStandardSurvivor (k:=k) R hB hQ)
      (nonsymmetricStandardSurvivor_injective R hB hQ)
  change LinearIndependent k (fun a : L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ) =>
    nonsymmetricColonPolynomialMap (k:=k) R hQ (monomial a.val 1))
  simp_rw [nonsymmetricColonPolynomialMap_monomial]
  unfold nonsymmetricPrincipalColonQuotient
  rw [nonsymmetric_principal_colon_eq_translated_carrier]
  exact hi

theorem nonsymmetricColonFactor_injective {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricColonFactor (k:=k) R hB hQ) := by
  let b := L3A.standardBasis _ (nonsymmetric_polynomial_colon_isMonomial (k:=k) R hB hQ)
  have he : b.constr k (fun a => nonsymmetricColonFactor R hB hQ (b a))=
      (nonsymmetricColonFactor (k:=k) R hB hQ).toLinearMap := by
    apply b.ext
    intro a
    simp
  have hi := b.injective_constr_of_linearIndependent (R₂:=k)
    (show LinearIndependent k (fun a => nonsymmetricColonFactor R hB hQ (b a)) from
      by simpa only [b,L3A.standardBasis,Module.Basis.mk_apply] using
        nonsymmetricColonFactor_standard_independent (k:=k) R hB hQ)
  rw [he] at hi
  exact hi

theorem nonsymmetric_principal_colon_eval_kernel {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    RingHom.ker (nonsymmetricColonPolynomialMap (k:=k) R hQ).toRingHom =
      nonsymmetricPolynomialColonIdeal k R hB hQ := by
  apply le_antisymm
  · intro p hp
    change nonsymmetricColonPolynomialMap (k:=k) R hQ p=0 at hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply nonsymmetricColonFactor_injective R hB hQ
    change nonsymmetricColonPolynomialMap (k:=k) R hQ p=nonsymmetricColonFactor R hB hQ 0
    simpa only [map_zero] using hp
  · exact nonsymmetric_polynomial_colon_le_eval_kernel R hB hQ

def nonsymmetricPrincipalColonAlgEquiv {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    (MvPolynomial (Fin 3) k ⧸ nonsymmetricPolynomialColonIdeal k R hB hQ) ≃ₐ[k]
      nonsymmetricPrincipalColonQuotient k R hQ :=
  AlgEquiv.ofBijective (nonsymmetricColonFactor R hB hQ)
    ⟨nonsymmetricColonFactor_injective R hB hQ,nonsymmetricColonFactor_surjective R hB hQ⟩

theorem nonsymmetric_Q_positive (R : SectorBCriticalRoleBranchB P) :
    0 < actualPrincipalIndex P.M.base := (actualPrincipalIndex_spec P.M.base).1

theorem nonsymmetric_Q_partition (R : SectorBCriticalRoleBranchB P) :
    actualPrincipalIndex P.M.base ≤ 2 ∨ 2 < actualPrincipalIndex P.M.base := by omega

/-- These are the images of the actual three tail generators, not abstract
symbols with an assumed identification to the colon algebra. -/
def nonsymmetricColonGenerators {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base)
    (i : Fin 3) : nonsymmetricPrincipalColonQuotient k R hQ :=
  Ideal.Quotient.mkₐ k (nonsymmetricPrincipalColonIdeal k R hQ)
    (AddMonoidAlgebra.single (nonsymmetricTailMonomialDegree R i) 1)

theorem nonsymmetricColonGenerators_eq_eval_X {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3) :
    nonsymmetricColonGenerators (k:=k) R hQ i=nonsymmetricColonPolynomialMap R hQ (X i) := by
  simp only [nonsymmetricColonPolynomialMap,aeval_X,nonsymmetricColonGenerators]

abbrev nonsymmetricPrincipalColonH0 {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  LinearMap.ker (threeKoszulD0 (k:=k) (nonsymmetricColonGenerators (k:=k) R hQ))

abbrev nonsymmetricPrincipalColonH1 {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  ThreeKoszulH1 (k:=k) (nonsymmetricColonGenerators (k:=k) R hQ)

theorem nonsymmetric_colon_finite {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.Finite k (nonsymmetricPrincipalColonQuotient k R hQ) := by
  unfold nonsymmetricPrincipalColonQuotient
  rw [nonsymmetric_principal_colon_eq_translated_carrier]
  exact carrierMonomialQuotient_finite _

theorem nonsymmetric_colon_H1_finite {k : Type*} [Field k]
    (R : SectorBCriticalRoleBranchB P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.Finite k (nonsymmetricPrincipalColonH1 (k:=k) R hQ) := by
  letI := nonsymmetric_colon_finite (k:=k) R hQ
  unfold nonsymmetricPrincipalColonH1 ThreeKoszulH1
  infer_instance

end NS25Lean.L5A2BFinalRepair
