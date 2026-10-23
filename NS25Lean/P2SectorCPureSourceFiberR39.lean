import NS25Lean.P2SectorCPureTailPrincipalR39

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR39
open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A
  L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR3 L5A2C4OR19 L5A2C4OR20
  L5A2C4OR29 FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

/-- D6 primitive: the actual boundary critical degree cannot divide an
actual minimal source degree in H.  The proper predecessor is extracted
from the killed component, not supplied by the caller. -/
theorem pure_source_boundary_divisor_impossible (P : P2Data Gamma)
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3) (s : ModelSources P.M.base e)
    {h k : ℕ} (hscale : routingD P.M.base e*h = G.boundaryDegree)
    (hk : k ∈ routingH P.M.base e) (he : s.val=h+k) : False := by
  obtain ⟨K,_⟩ := Nat.card_eq_one_iff_exists.mp G.boundarySignature.2
  obtain ⟨u,_,j,huj,hpred⟩ := K.property
  obtain ⟨i,rfl⟩ := e.surjective j
  let B := P.M.base
  let g : ℕ := ![routingA B e,routingB B e,routingC B e] i
  have hgscale : routingD B e*g = weights B (e i) := by
    fin_cases i
    · simpa [g,normalizedGrid,gridDegree] using normalizedGrid_scale B e 1 0 0
    · simpa [g,normalizedGrid,gridDegree] using normalizedGrid_scale B e 0 1 0
    · simpa [g,normalizedGrid,gridDegree] using normalizedGrid_scale B e 0 0 1
  have hD : 0 < routingD B e := tailGcd_pos (weights_positive B (e 0))
  have hgpos : 0 < g := by
    have hp := weights_positive B (e i)
    rw [←hgscale] at hp
    nlinarith
  have hgH : g ∈ routingH B e := by
    fin_cases i
    · simpa [g,monomialDegree,normalizedGrid] using L5A2C4OR33.grid_mem_H B e (1,0,0)
    · simpa [g] using routingHB B e
    · simpa [g] using routingHC B e
  have hw : weights B (e i) ≤ G.boundaryDegree := by
    have hs : u.val (e i)*weights B (e i) ≤ ∑ j, u.val j*weights B j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (u.val j*weights B j))
        (Finset.mem_univ (e i))
    rw [←weight_eq_sum,u.property] at hs
    exact (Nat.le_mul_of_pos_left _ huj).trans hs
  have hgle : g ≤ h := by
    change routingD B e*h = G.boundaryDegree at hscale
    rw [←hgscale,←hscale] at hw
    nlinarith
  have hpred' : h-g ∈ cyclicCut (routingH B e) (routingM B e) := by
    apply (actual_scaled_cut_iff B e (h-g)).mpr
    rw [Nat.mul_sub_left_distrib,hscale,hgscale]
    exact hpred
  exact source_forbids_critical_divisor B e s hpred' hgle hgH hgpos hk he

private theorem pair_degree_scale {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P) :
    routingD P.M.base A.reindex * (alpha A*routingB P.M.base A.reindex) =
      A.pairDegree := by
  have hs := (branchA_symmetricTailData A).c1_eq_alpha
  have he := A.pair.right_degree_eq_critical
  rw [←A.reindex_one] at he
  have hb : routingD P.M.base A.reindex*routingB P.M.base A.reindex =
      weights P.M.base (A.reindex 1) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base A.reindex 0 1 0
  change criticalExponent P.M.base (A.reindex 1)=alpha A at hs
  rw [hs] at he
  rw [he,←hb]
  ring

/-- No factorization of any source can contain the boundary pure relation. -/
theorem boundary_pair_source_y_lt (P : P2Data Gamma) (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hp : A.pairDegree=G.boundaryDegree)
    (v : ModelSources P.M.base A.reindex) (z : Monomial)
    (hz : monomialDegree P.M.base A.reindex z=v.val) : z.2.1 < alpha A := by
  by_contra hn
  have hy : alpha A ≤ z.2.1 := by omega
  have hscale := (pair_degree_scale A).trans hp
  have hmul := congrArg (fun t => t*routingB P.M.base A.reindex) (Nat.sub_add_cancel hy)
  apply pure_source_boundary_divisor_impossible P G A.reindex v hscale
    (L5A2C4OR33.grid_mem_H P.M.base A.reindex (z.1,z.2.1-alpha A,z.2.2))
  simp only [monomialDegree,normalizedGrid,Nat.add_mul] at hz hmul ⊢
  omega

/-- D6 source-fiber generation by the internal mixed binomial only, at the
original physical P/G.  First-principal sources are included. -/
theorem boundary_pair_source_fiber_internal (P : P2Data Gamma) (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hp : A.pairDegree=G.boundaryDegree)
    (k : Type*) [Field k] (v : ModelSources P.M.base A.reindex) {z w : Monomial}
    (hz : monomialDegree P.M.base A.reindex z=v.val)
    (hw : monomialDegree P.M.base A.reindex w=v.val) :
    roleMonomial k A.reindex z-roleMonomial k A.reindex w ∈ Ideal.span
      {roleMonomial k A.reindex (0,0,d A)-roleMonomial k A.reindex (r A,s A,0)} := by
  let I : Ideal (ToricPresentation.Poly k 3) := Ideal.span
    {roleMonomial k A.reindex (0,0,d A)-roleMonomial k A.reindex (r A,s A,0)}
  let q (t : Monomial) := Ideal.Quotient.mk I (roleMonomial k A.reindex t)
  have qadd (t u : Monomial) : q (t+u)=q t*q u := by
    simp only [q,roleMonomial_add,map_mul]
  have qrel : q (0,0,d A)=q (r A,s A,0) :=
    Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hd : 0 < d A := by
    have h := (branchA_symmetricTailData A).n0_pos
    rw [(branchA_symmetricTailData A).n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have normal (t : Monomial) (ht : monomialDegree P.M.base A.reindex t=v.val) :
      ∃ u : Monomial, u.2.1<alpha A ∧ u.2.2<d A ∧
        monomialDegree P.M.base A.reindex u=v.val ∧ q t=q u := by
    obtain ⟨x,y,z⟩ := t
    induction z using Nat.strong_induction_on generalizing x y with
    | h z ih =>
      by_cases hzd : d A ≤ z
      · have hstep := pure_tail_mixed_step_degree A x y z hzd
        have ht' := hstep.symm.trans ht
        obtain ⟨u,huy,huz,hdeg,hq⟩ := ih (z-d A) (by omega) (x+r A) (y+s A) ht'
        refine ⟨u,huy,huz,hdeg,?_⟩
        have h1 : (x,y,z)=(x,y,z-d A)+(0,0,d A) := by ext <;> simp <;> omega
        have h2 : (x+r A,y+s A,z-d A)=(x,y,z-d A)+(r A,s A,0) := by ext <;> simp
        have hctx : q (x,y,z)=q (x+r A,y+s A,z-d A) := by
          rw [h1,h2,qadd,qadd,qrel]
        exact hctx.trans hq
      · exact ⟨(x,y,z),boundary_pair_source_y_lt P G A hp v _ ht,Nat.lt_of_not_ge hzd,ht,rfl⟩
  obtain ⟨z',hzy,hzz,hzd,hzq⟩ := normal z hz
  obtain ⟨w',hwy,hwz,hwd,hwq⟩ := normal w hw
  have heq := pure_tail_normal_unique A ⟨hzy,hzz⟩ ⟨hwy,hwz⟩ (hzd.trans hwd.symm)
  apply Ideal.Quotient.eq.mp
  exact hzq.trans (by rw [heq]; exact hwq.symm)

private theorem mixed_degree_scale {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P) :
    routingD P.M.base A.reindex * (d A*routingC P.M.base A.reindex) =
      A.mixedDegree := by
  have hs := (branchA_symmetricTailData A).c2_eq_d
  have he := A.mixed.degree_eq_critical
  rw [←A.reindex_two] at he
  have hc : routingD P.M.base A.reindex*routingC P.M.base A.reindex =
      weights P.M.base (A.reindex 2) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base A.reindex 0 0 1
  change criticalExponent P.M.base (A.reindex 2)=d A at hs
  rw [hs] at he
  rw [he,←hc]
  ring

/-- The boundary pure/mixed degree is excluded in the internal-pure case. -/
theorem internal_pair_source_z_lt (P : P2Data Gamma) (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hp : A.mixedDegree=G.boundaryDegree)
    (v : ModelSources P.M.base A.reindex) (z : Monomial)
    (hz : monomialDegree P.M.base A.reindex z=v.val) : z.2.2 < d A := by
  by_contra hn
  have hj : d A ≤ z.2.2 := by omega
  have hscale := (mixed_degree_scale A).trans hp
  have hmul := congrArg (fun t => t*routingC P.M.base A.reindex) (Nat.sub_add_cancel hj)
  apply pure_source_boundary_divisor_impossible P G A.reindex v hscale
    (L5A2C4OR33.grid_mem_H P.M.base A.reindex (z.1,z.2.1,z.2.2-d A))
  simp only [monomialDegree,normalizedGrid,Nat.add_mul] at hz hmul ⊢
  omega

/-- D6 mirror: at any source only the internal pure relation remains. -/
theorem internal_pair_source_fiber_internal (P : P2Data Gamma) (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hp : A.mixedDegree=G.boundaryDegree)
    (k : Type*) [Field k] (v : ModelSources P.M.base A.reindex) {z w : Monomial}
    (hz : monomialDegree P.M.base A.reindex z=v.val)
    (hw : monomialDegree P.M.base A.reindex w=v.val) :
    roleMonomial k A.reindex z-roleMonomial k A.reindex w ∈ Ideal.span
      {roleMonomial k A.reindex (0,alpha A,0)-roleMonomial k A.reindex (beta A,0,0)} := by
  let I : Ideal (ToricPresentation.Poly k 3) := Ideal.span
    {roleMonomial k A.reindex (0,alpha A,0)-roleMonomial k A.reindex (beta A,0,0)}
  let q (t : Monomial) := Ideal.Quotient.mk I (roleMonomial k A.reindex t)
  have qadd (t u : Monomial) : q (t+u)=q t*q u := by
    simp only [q,roleMonomial_add,map_mul]
  have qrel : q (0,alpha A,0)=q (beta A,0,0) :=
    Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))
  have ha : 0 < alpha A := by
    have h := (branchA_symmetricTailData A).n0_pos
    rw [(branchA_symmetricTailData A).n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have normal (t : Monomial) (ht : monomialDegree P.M.base A.reindex t=v.val) :
      ∃ u : Monomial, u.2.1<alpha A ∧ u.2.2<d A ∧
        monomialDegree P.M.base A.reindex u=v.val ∧ q t=q u := by
    obtain ⟨x,y,z⟩ := t
    induction y using Nat.strong_induction_on generalizing x with
    | h y ih =>
      by_cases hya : alpha A ≤ y
      · have hstep := pure_tail_pure_step_degree A x y z hya
        have ht' := hstep.symm.trans ht
        obtain ⟨u,huy,huz,hdeg,hq⟩ := ih (y-alpha A) (by omega) (x+beta A) ht'
        refine ⟨u,huy,huz,hdeg,?_⟩
        have h1 : (x,y,z)=(x,y-alpha A,z)+(0,alpha A,0) := by ext <;> simp <;> omega
        have h2 : (x+beta A,y-alpha A,z)=(x,y-alpha A,z)+(beta A,0,0) := by ext <;> simp
        have hctx : q (x,y,z)=q (x+beta A,y-alpha A,z) := by
          rw [h1,h2,qadd,qadd,qrel]
        exact hctx.trans hq
      · exact ⟨(x,y,z),Nat.lt_of_not_ge hya,internal_pair_source_z_lt P G A hp v _ ht,ht,rfl⟩
  obtain ⟨z',hzy,hzz,hzd,hzq⟩ := normal z hz
  obtain ⟨w',hwy,hwz,hwd,hwq⟩ := normal w hw
  have heq := pure_tail_normal_unique A ⟨hzy,hzz⟩ ⟨hwy,hwz⟩ (hzd.trans hwd.symm)
  apply Ideal.Quotient.eq.mp
  exact hzq.trans (by rw [heq]; exact hwq.symm)

private theorem source_rectangle_exists {P : P2Data Gamma}
    (A : SectorBCriticalRoleBranchA P) (v : ModelSources P.M.base A.reindex) :
    ∃ z : Monomial, monomialDegree P.M.base A.reindex z=v.val ∧
      z.2.1<alpha A ∧ z.2.2<d A := by
  obtain ⟨x,y,z,hy,hz,he⟩ := L5A2B4AR5A.branchA_routingH_rectangle_factorization
    A v.property.1.1
  exact ⟨(x,y,z),he.symm,hy,hz⟩

/-- A genuine actual source representative selected from the proved unique
rectangle normal form.  This definition is not a gate/count premise. -/
def pureSourceNormal {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P)
    (v : ModelSources P.M.base A.reindex) : Monomial :=
  Classical.choose (source_rectangle_exists A v)

theorem pureSourceNormal_spec {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P)
    (v : ModelSources P.M.base A.reindex) :
    monomialDegree P.M.base A.reindex (pureSourceNormal A v)=v.val ∧
      (pureSourceNormal A v).2.1<alpha A ∧ (pureSourceNormal A v).2.2<d A :=
  Classical.choose_spec (source_rectangle_exists A v)

theorem pureSourceNormal_injective {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P) :
    Function.Injective (pureSourceNormal A) := by
  intro v w he
  apply Subtype.ext
  exact (pureSourceNormal_spec A v).1.symm.trans
    ((congrArg (monomialDegree P.M.base A.reindex) he).trans (pureSourceNormal_spec A w).1)

/-- The proposed D6 ideal in the killed-x/alive-y boundary orientation:
internal mixed relation, actual unique source normals, and the alive y-axis
boundary monomial.  Equality to the original J is not asserted by this def. -/
def pureBoundarySourceIdeal {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P)
    (k : Type*) [Field k] : Ideal (ToricPresentation.Poly k 3) :=
  Ideal.span ({roleMonomial k A.reindex (0,0,d A)-roleMonomial k A.reindex (r A,s A,0)} ∪
    Set.range (fun v : ModelSources P.M.base A.reindex => roleMonomial k A.reindex (pureSourceNormal A v)) ∪
    {roleMonomial k A.reindex (0,alpha A,0)})

end NS25Lean.L5A2C4OR39
