import NS25Lean.MonomialActualRigidity
set_option linter.style.header false
noncomputable section
namespace NS25Lean.MonomialPivotStrictness
open ChosenBase L2B L2B2A L2B2A2 L3A L3B L3C L5A1 L5A2R49First
open MvPolynomial
variable {Gamma : NumericalSemigroup}
/-- D-1, first graph step.  A live component contains only one actual
factorization: an edge inside it would give two factorizations of an actual
immediate predecessor. -/
theorem live_component_unique_rep (M : MultiplicityBase Gamma) (h : ℕ)
    (C : FiberComponent M.base h) (hlive : ¬ BoundaryKilled M h C)
    (hunique : ∀ d, d ∈ M.base.apery → Subsingleton (FactorizationFiber M.base d))
    (u v : FactorizationFiber M.base h)
    (hu : (fiberGraph M.base h).connectedComponentMk u = C)
    (hv : (fiberGraph M.base h).connectedComponentMk v = C) : u = v := by
  by_contra huv
  have hr : (fiberGraph M.base h).Reachable u v :=
    SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)
  obtain ⟨p, _hp⟩ := hr.exists_isPath
  have hpn : ¬p.Nil := p.not_nil_of_ne huv
  have hadj : (fiberGraph M.base h).Adj u p.snd := p.adj_snd hpn
  rcases hadj with ⟨hus, j, huj, hsj⟩
  have hsC : (fiberGraph M.base h).connectedComponentMk p.snd = C := by
    exact (SimpleGraph.ConnectedComponent.sound
      (show (fiberGraph M.base h).Reachable u p.snd from
        ⟨(SimpleGraph.Walk.cons ⟨hus, j, huj, hsj⟩ SimpleGraph.Walk.nil)⟩)).symm.trans hu
  have hurem := removed_weight M.base h u j huj
  have hsrem := removed_weight M.base h p.snd j hsj
  have hap : h - weights M.base j ∈ M.base.apery := by
    rw [M.base.apery_eq_compl]
    refine ⟨?_, ?_⟩
    · have hm := (Presentation.factorizationMap M.base.tailDegrees
        (u.val - Finsupp.single j 1)).property
      rw [← weight_eq_degree] at hm
      convert hm using 1 <;> omega
    · intro hk
      exact hlive ⟨u, hu, j, huj, hk⟩
  let u' : FactorizationFiber M.base (h - weights M.base j) :=
    ⟨u.val - Finsupp.single j 1, by omega⟩
  let s' : FactorizationFiber M.base (h - weights M.base j) :=
    ⟨p.snd.val - Finsupp.single j 1, by omega⟩
  have he := congrArg Subtype.val ((hunique _ hap).elim u' s')
  have he' := congrArg (fun w => Finsupp.single j 1 + w) he
  apply hus
  apply Subtype.ext
  simpa only [u', s', remove_variable_add u.val j huj,
    remove_variable_add p.snd.val j hsj] using he'

/-- A live component at a boundary degree contributes an actual minimal
excluded monomial. No contribution or defect bound is an input. -/
theorem live_component_minimal_exponent (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) (hhK : h∈M.base.K)
    (C : FiberComponent M.base h) (hlive : ¬BoundaryKilled M h C)
    (hJ : IsMonomialIdeal k (M.base.J k)) :
    ∃ u : FactorizationFiber M.base h,
      (fiberGraph M.base h).connectedComponentMk u=C ∧
      u.val∈minimalExponents (M.base.J k) := by
  have hJM := monomial_eq_MK k M.base hJ
  classical
  obtain ⟨u, huC⟩ := C.exists_rep
  have huJ : MvPolynomial.monomial u.val (1 : k) ∈ M.base.J k :=
    boundary_monomial_mem_J k M.base u.val (u.property.symm ▸ hhK)
  have humin : u.val ∈ minimalExponents (M.base.J k) := by
    refine ⟨huJ, ?_⟩
    intro v hvJ hvu
    have hvMK : MvPolynomial.monomial v (1 : k) ∈ M.base.MK k := hJM ▸ hvJ
    rw [Data.MK] at hvMK
    obtain ⟨w, hwK, hwv⟩ := (monomial_mem_span_iff _ v).mp hvMK
    have hwu : w ≤ u.val := le_trans hwv hvu
    intro j
    by_contra hn
    have hvjlt : v j < u.val j := by
      have := hvu j
      omega
    have huj : 0 < u.val j := by omega
    let pred := u.val - Finsupp.single j 1
    have hwp : w ≤ pred := by
      intro x
      simp only [pred, Finsupp.tsub_apply]
      by_cases hx : x = j
      · subst x
        simp only [Finsupp.single_eq_same]
        have h1 := hwv j
        omega
      · simp only [Finsupp.single_eq_of_ne hx]
        exact hwu x
    have hpredK : weight M.base pred ∈ M.base.K := by
      have hadd := FourGeneratedBridge.aperyTail_add_mem M.base.H_le hwK
        (weight_mem_H M.base (pred - w))
      have hadd' : weight M.base w + weight M.base (pred - w) ∈ M.base.K := by
        simpa only [Data.K, weight_eq_degree] using hadd
      have he := congrArg (weight M.base) (add_tsub_cancel_of_le hwp)
      rw [map_add] at he
      exact he ▸ hadd'
    exact hlive ⟨u, huC, j, huj, by
      have hrem := removed_weight M.base h u j huj
      have hp : weight M.base pred = h - weights M.base j := by
        change weights M.base j + weight M.base pred = h at hrem
        omega
      rwa [← hp]⟩
  exact ⟨u,huC,humin⟩

theorem positive_degree_boundary (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (hJ : IsMonomialIdeal k (M.base.J k))
    (h : ℕ) (hp : 0<fiberContribution M h) : h∈M.base.K := by
  classical
  have hc := (positive_contribution_active M h hp).2
  have hn : Nonempty (FiberComponent M.base h) :=
    (Nat.card_pos_iff.mp (show 0<Nat.card (FiberComponent M.base h) by
      change 0<componentCount M.base h; omega)).1
  obtain ⟨C⟩ := hn
  obtain ⟨u,hu⟩ := C.exists_rep
  by_contra hk
  have ha : h∈M.base.apery := M.base.apery_eq_compl.symm ▸
    ⟨u.property ▸ weight_mem_H M.base u.val,hk⟩
  haveI := monomial_apery_unique k M.base hJ h ha
  haveI : Subsingleton (FiberComponent M.base h) := inferInstance
  have hle : Nat.card (FiberComponent M.base h)≤1 := by
    simpa using Nat.card_le_card_of_injective (fun _ : FiberComponent M.base h => ())
      (fun a b _ => Subsingleton.elim a b)
  change componentCount M.base h≤1 at hle
  omega

theorem positive_has_live_component (M : MultiplicityBase Gamma)
    (h : ℕ) (hp : 0<fiberContribution M h) :
    ∃ C : FiberComponent M.base h, ¬BoundaryKilled M h C := by
  classical
  by_contra hn
  push Not at hn
  have hle : componentCount M.base h≤killedCount M h :=
    Nat.card_le_card_of_injective (fun C => (⟨C,hn C⟩ :
      {C : FiberComponent M.base h // BoundaryKilled M h C}))
      (fun a b he => congrArg Subtype.val he)
  have hc := (positive_contribution_active M h hp).2
  unfold fiberContribution at hp
  split_ifs at hp <;> omega

/-- The actual positive-contribution support supplies a nonuniquely factored
minimal pure monomial, using live components and actual Apéry uniqueness. -/
theorem positive_has_nonunique_pure (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (hJ : IsMonomialIdeal k (M.base.J k))
    (g : Exponent) (hg : g∈fullSupportGenerators (M.base.J k))
    (h : ℕ) (hp : 0<fiberContribution M h) :
    ∃ (i : Fin 3) (A : ℕ) (v : Exponent), 0<A ∧
      h=A*weights M.base i ∧ Finsupp.single i A∈minimalExponents (M.base.J k) ∧
      v i=0 ∧ weight M.base v=h := by
  classical
  have hJM := monomial_eq_MK k M.base hJ
  have hunique := monomial_apery_unique k M.base hJ
  have hqle := chosen_q_fs_le_one M.base MonomialOrder.degLex hJ
  have hqpos : 0<q_fs (M.base.J k) :=
    (Set.ncard_pos (fullSupportGenerators_finite _)).mpr ⟨g,hg⟩
  have hq : q_fs (M.base.J k)=1 := by omega
  obtain ⟨C,hlive⟩ := positive_has_live_component M h hp
  obtain ⟨u,hu,humin⟩ := live_component_minimal_exponent k M h
    (positive_degree_boundary k M hJ h hp) C hlive hJ
  obtain ⟨K,hKC⟩ : ∃ K : FiberComponent M.base h, K≠C := by
    by_contra hn
    push Not at hn
    haveI : Subsingleton (FiberComponent M.base h) := ⟨fun a b => (hn a).trans (hn b).symm⟩
    have hle : Nat.card (FiberComponent M.base h)≤1 := by
      simpa using Nat.card_le_card_of_injective (fun _ : FiberComponent M.base h => ())
        (fun a b _ => Subsingleton.elim a b)
    have hc := (positive_contribution_active M h hp).2
    change componentCount M.base h≤1 at hle
    omega
  obtain ⟨v,hv⟩ := K.exists_rep
  have hvu : v.val≠u.val := by
    intro he
    exact hKC (hv.symm.trans ((congrArg (fiberGraph M.base h).connectedComponentMk
      (Subtype.ext he)).trans hu))
  obtain ⟨i,hui,huoff⟩ := nonunique_minimal_border_pure k M.base hJ hJM hunique
    hq g u.val v.val hg humin (v.property.trans u.property.symm) hvu
  have huform : u.val=Finsupp.single i (u.val i) := by
    ext j
    by_cases hji : j=i
    · subst j; simp
    · simp [hji,huoff j hji]
  refine ⟨i,u.val i,v.val,hui,?_,huform ▸ humin,?_,v.property⟩
  · calc
      h=weight M.base u.val := u.property.symm
      _=weight M.base (Finsupp.single i (u.val i)) := congrArg (weight M.base) huform
      _=u.val i*weights M.base i := weight_single _ _ _
  · exact minimal_factorization_disjoint k M.base hJ u.val v.val humin
      (v.property.trans u.property.symm) hvu i hui

end NS25Lean.MonomialPivotStrictness
