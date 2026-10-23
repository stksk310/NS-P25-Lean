import NS25Lean.P2BranchBPrefixGeometry

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

theorem nonsymmetric_generators_positive (R : SectorBCriticalRoleBranchB P) :
    0 < nsA R ∧ 0 < nsB R ∧ 0 < nsC R := by
  have ha := routingA_pos P.M.base (nsReindex R)
  change 0 < nsA R at ha
  have hp := nonsymmetric_coefficients R
  have hr := nonsymmetric_normalized_relations R
  have hb := hr.2.1
  have hc := hr.2.2
  refine ⟨ha,?_,?_⟩
  · by_contra hn
    have hz : nsB R=0 := by omega
    rw [hz,mul_zero] at hb
    have hpos := Nat.mul_pos hp.2.2.1 ha
    omega
  · by_contra hn
    have hz : nsC R=0 := by omega
    rw [hz,mul_zero] at hc
    have hpos := Nat.mul_pos hp.2.2.2.2.1 ha
    omega

/-- First critical minimality in the inactive chart, via the actual cyclic dictionary. -/
theorem nonsymmetric_a_relation_min (R : SectorBCriticalRoleBranchB P)
    {n x y : ℕ} (hp : 0 < n) (hr : n*nsA R=x*nsB R+y*nsC R) : nsC1 R ≤ n := by
  apply branchB_normalizedC_relation_min R n x y hp
  simpa only [nsA,nsB,nsC,nsReindex,branchB_inactive_routingA_eq_normalizedC,
    branchB_inactive_routingB_eq_normalizedA,branchB_inactive_routingC_eq_normalizedB] using hr

theorem nonsymmetric_subcritical_a_factorization (R : SectorBCriticalRoleBranchB P)
    {n t x y : ℕ} (hn : n < nsC1 R)
    (he : n*nsA R=t*nsA R+x*nsB R+y*nsC R) : t=n ∧ x=0 ∧ y=0 := by
  have hp := nonsymmetric_generators_positive R
  have ht : t ≤ n := by nlinarith
  have hte : t=n := by
    by_contra hnot
    have hpos : 0 < n-t := by omega
    have hsub := Nat.sub_add_cancel ht
    have hrel : (n-t)*nsA R=x*nsB R+y*nsC R := by nlinarith only [he,congrArg (fun z => z*nsA R) hsub]
    have hh := nonsymmetric_a_relation_min R hpos hrel
    omega
  rw [hte] at he
  exact ⟨hte,by nlinarith,by nlinarith⟩

private theorem subcritical_divisor_components (R : SectorBCriticalRoleBranchB P)
    {n t x y : ℕ} (hn : n < nsC1 R)
    (hd : ((n*nsA R : ℕ) : ℤ)-(t*nsA R+x*nsB R+y*nsC R : ℕ) ∈ (nsH R).asRelativeIdeal) : x=0 ∧ y=0 := by
  obtain ⟨w,hw,he⟩ := hd
  obtain ⟨a,b,c,hf⟩ := L5A2C4OR6.routingH_factorization P.M.base (nsReindex R) hw
  change w=a*nsA R+b*nsB R+c*nsC R at hf
  have heN : n*nsA R=(t+a)*nsA R+(x+b)*nsB R+(y+c)*nsC R := by
    rw [hf] at he
    simp only [Nat.cast_add,Nat.cast_mul] at he
    exact_mod_cast (show (n : ℤ)*nsA R=(t+a)*nsA R+(x+b)*nsB R+(y+c)*nsC R by nlinarith only [he])
  have hh := nonsymmetric_subcritical_a_factorization R hn heN
  omega

/-- A prefix divisor of a subcritical pure a point yields the inclusive
origin return, including the boundary i=p / j=q degenerations. -/
theorem nonsymmetric_subcritical_a_prefix_origin (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    {n : ℕ} (hn : n < nsC1 R)
    (hm : ((n*nsA R : ℕ) : ℤ) ∈ nonsymmetricPrefixIdeal R hQ) :
    ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 ≤ nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 ≤ nsQ R := by
  obtain ⟨ell,hz⟩ := (nonsymmetric_prefix_four_sources R hB hQ _).mp hm
  have S := nonsymmetricReturnTuple_spec R hB ell
  let t := nonsymmetricReturnTuple R hB ell
  have hi : 0 < t.1 := S.2.1
  have hj : 0 < t.2.1 := S.2.2.1
  rcases hz with hf | hx | hy | ⟨hi',hj',_⟩
  · have hh := subcritical_divisor_components R hn (t:=0) (x:=t.1) (y:=t.2.1)
      (by simpa only [zero_mul,zero_add] using hf)
    omega
  · by_cases hit : t.1 < nsP R
    · dsimp only [t] at hit
      have hh := subcritical_divisor_components R hn (t:=nsW R-t.2.2) (x:=t.1+nsZ R) (y:=0)
        (by simpa only [t,nonsymmetricX,ite_eq_left hit,zero_mul,add_zero] using hx)
      omega
    · dsimp only [t] at hit
      have hh := subcritical_divisor_components R hn (t:=nsC1 R-t.2.2) (x:=t.1-nsP R) (y:=0)
        (by simpa only [t,nonsymmetricX,ite_eq_right hit,zero_mul,add_zero] using hx)
      have hd := S.1.2.2
      exact ⟨ell,by dsimp [t] at hh ⊢; omega,by omega⟩
  · by_cases hjt : t.2.1 < nsQ R
    · dsimp only [t] at hjt
      have hh := subcritical_divisor_components R hn (t:=nsU R-t.2.2) (x:=0) (y:=t.2.1+nsV R)
        (by simpa only [t,nonsymmetricY,ite_eq_left hjt,zero_mul,add_zero] using hy)
      omega
    · dsimp only [t] at hjt
      have hh := subcritical_divisor_components R hn (t:=nsC1 R-t.2.2) (x:=0) (y:=t.2.1-nsQ R)
        (by simpa only [t,nonsymmetricY,ite_eq_right hjt,zero_mul,add_zero] using hy)
      have hd := S.1.2.2
      exact ⟨ell,by omega,by dsimp [t] at hh ⊢; omega⟩
  · exact ⟨ell,le_of_lt hi',le_of_lt hj'⟩

theorem nonsymmetric_routingI_mem_split (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : ℤ) :
    z ∈ routingI P.M.base (nsReindex R) ↔
    z ∈ nonsymmetricPrefixIdeal R hQ ∨
      z-(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) ∈ (nsH R).asRelativeIdeal := by
  rw [mem_normalizedTailIdeal_iff_positive_return (chosenBase_minimalFour P.M.base (nsReindex R))]
  change z ∈ positiveReturnCarrier (nsH R) (normalizedM P.M.base) ↔ _
  rw [positiveReturnCarrier_eq_finalCarrier (nsH R) (normalizedM P.M.base) P.M.base.q_positive]
  have he : principalIndex (nsH R) (normalizedM P.M.base) P.M.base.q_positive=actualPrincipalIndex P.M.base := by
    rw [nonsymmetric_H_eq_normalizedH R]
  rw [he]
  rfl

private theorem subcritical_a_divisor_pure (R : SectorBCriticalRoleBranchB P)
    {n g : ℕ} (hn : n < nsC1 R) (hg : g ∈ nsH R)
    (hd : ((n*nsA R : ℕ) : ℤ)-(g : ℕ) ∈ (nsH R).asRelativeIdeal) :
    ∃ t : ℕ, g=t*nsA R := by
  obtain ⟨a,b,c,hf⟩ := L5A2C4OR6.routingH_factorization P.M.base (nsReindex R) hg
  change g=a*nsA R+b*nsB R+c*nsC R at hf
  have hh := subcritical_divisor_components R hn (hf ▸ hd)
  exact ⟨a,by simpa only [hh.1,hh.2,zero_mul,add_zero] using hf⟩

/-- N2-A's inclusive origin witness. Principal insertion is retained;
its pure-a branch is excluded only at the actual canonical seam point. -/
theorem nonsymmetric_inclusive_origin_return (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 ≤ nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 ≤ nsQ R := by
  have hc := nonsymmetric_coefficients R
  have ha := nonsymmetric_generators_positive R
  have hfloor := branchB_inactive_H0_lt R
  change eta P.M.base (nsReindex R) 0 0 < nsC1 R at hfloor
  have hmem : (((nsC1 R-1)*nsA R : ℕ) : ℤ) ∈ routingI P.M.base (nsReindex R) := by
    have hm := (normalizedGrid_mem_iff_eta_le P.M.base (nsReindex R) (nsC1 R-1) 0 0).mpr (by omega)
    simpa only [normalizedGrid,zero_mul,add_zero] using hm
  rcases (nonsymmetric_routingI_mem_split R hQ _).mp hmem with hp | hf
  · exact nonsymmetric_subcritical_a_prefix_origin R hB hQ (by omega) hp
  have hg := (nonsymmetricPrincipalDegree R).property
  obtain ⟨t,ht⟩ := subcritical_a_divisor_pure R (by omega) hg hf
  have htp : 0 < t := by
    have hQp := (actualPrincipalIndex_spec P.M.base).1
    change actualPrincipalIndex P.M.base*normalizedM P.M.base=t*nsA R at ht
    have hmp := P.M.base.q_positive
    change 0 < normalizedM P.M.base at hmp
    nlinarith [Nat.mul_pos hQp hmp]
  have seam (x y : ℕ) (hd : NonsymmetricLDomain R x y)
      (hm : ((x*nsB R+y*nsC R : ℕ) : ℤ) ∈ routingI P.M.base (nsReindex R))
      (hx : x ≤ nsP R) (hy : y ≤ nsQ R) :
      ∃ ell : NonsymmetricReturnIndex R,
        (nonsymmetricReturnTuple R hB ell).1 ≤ nsP R ∧
        (nonsymmetricReturnTuple R hB ell).2.1 ≤ nsQ R := by
    rcases (nonsymmetric_routingI_mem_split R hQ _).mp hm with hp | hf'
    · obtain ⟨ell,hi,hj⟩ := (nonsymmetric_canonical_prefix_coordinates R hB hQ hd).mp hp
      exact ⟨ell,le_trans hi hx,le_trans hj hy⟩
    · apply (nonsymmetric_canonical_a_predecessor_not_mem R hd ?_).elim
      have hrem := nonsymmetric_grid_mem R (t-1) 0 0
      obtain ⟨w,hw,he⟩ := hrem
      have hadd := (nsH R).asRelativeIdeal.add_mem hf' hw
      have hti : ((t-1 : ℕ) : ℤ)+1=t := by omega
      have htZ : ((actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) : ℤ)=
          (t : ℤ)*nsA R := by exact_mod_cast ht
      simp only [zero_mul,add_zero,Nat.cast_mul] at he
      have htiA := congrArg (fun z : ℤ => z*(nsA R : ℤ)) hti
      simp only [add_mul,one_mul] at htiA
      have hval : ((x*nsB R+y*nsC R : ℕ) : ℤ)-nsA R=
          ((x*nsB R+y*nsC R : ℕ) : ℤ)-
            (actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)+(w : ℕ) := by
        linarith only [he,htZ,htiA]
      rw [hval]
      exact hadd
  rcases branchB_inactive_seam_zero R with hs | hs
  · change eta P.M.base (nsReindex R) (nsP R-1) (nsQ R)=0 at hs
    have hd : NonsymmetricLDomain R (nsP R-1) (nsQ R) := by
      unfold NonsymmetricLDomain; omega
    apply seam (nsP R-1) (nsQ R) hd _ (by omega) (by omega)
    have hm := (normalizedGrid_mem_iff_eta_le P.M.base (nsReindex R) 0 (nsP R-1) (nsQ R)).mpr (by omega)
    simpa only [normalizedGrid,zero_mul,zero_add] using hm
  · change eta P.M.base (nsReindex R) (nsP R) (nsQ R-1)=0 at hs
    have hd : NonsymmetricLDomain R (nsP R) (nsQ R-1) := by
      unfold NonsymmetricLDomain; omega
    apply seam (nsP R) (nsQ R-1) hd _ (by omega) (by omega)
    have hm := (normalizedGrid_mem_iff_eta_le P.M.base (nsReindex R) 0 (nsP R) (nsQ R-1)).mpr (by omega)
    simpa only [normalizedGrid,zero_mul,zero_add] using hm

end NS25Lean.L5A2BFinalRepair
