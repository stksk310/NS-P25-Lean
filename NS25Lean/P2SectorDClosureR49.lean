import NS25Lean.P2DAFirstReturnR49

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2R49D

open ChosenBase L2B L2B2A L2B2A2 L3A L3B L3C L5A1 L5A2R49First
open scoped MonomialOrder

variable {Gamma : NumericalSemigroup}

/-- R49 actual-object monomialization, including the MP-1 repair. -/
private theorem sectorD_monomial (k : Type*) [Field k] (P : P2Data Gamma)
    (hD : SectorD P.M) : IsMonomialIdeal k (P.M.base.J k) :=
  L5A2R49.sectorD_monomial P hD k

private theorem sectorD_boundary_payload (k : Type*) [Field k] (P : P2Data Gamma)
    (hD : SectorD P.M) : P.M.base.J k = P.M.base.MK k ∧
      ∀ d, d ∈ P.M.base.apery → Subsingleton (FactorizationFiber P.M.base d) :=
  ⟨L5A2R49.sectorD_J_eq_MK P hD k, L5A2R49.sectorD_apery_unique P hD⟩

private theorem sectorD_q_fs_dichotomy (k : Type*) [Field k] (P : P2Data Gamma)
    (hD : SectorD P.M) : q_fs (P.M.base.J k) = 0 ∨ q_fs (P.M.base.J k) = 1 := by
  have := chosen_q_fs_le_one P.M.base MonomialOrder.degLex (sectorD_monomial k P hD)
  omega

private theorem sectorD_target_of_q_fs_zero (k : Type*) [Field k] (P : P2Data Gamma)
    (hD : SectorD P.M) (hq : q_fs (P.M.base.J k) = 0) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  have hb := support_refined_monomial_type_bound
    (chosenArtinianMonomial P.M.base MonomialOrder.degLex (sectorD_monomial k P hD))
  change quotientType (P.M.base.J k) ≤ mu (P.M.base.J k) + q_fs (P.M.base.J k) - 2 at hb
  rw [chosen_type_eq, chosen_mu_eq, hq] at hb
  have := p2_rho_eq_sourceCount_add_two P
  omega

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

private theorem live_component_minimal_pure_gate (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ)
    (C K : FiberComponent M.base h) (hlive : ¬ BoundaryKilled M h C)
    (hkill : BoundaryKilled M h K) (hCK : C ≠ K)
    (hJ : IsMonomialIdeal k (M.base.J k)) (hJM : M.base.J k = M.base.MK k)
    (hunique : ∀ d, d ∈ M.base.apery → Subsingleton (FactorizationFiber M.base d))
    (hq : q_fs (M.base.J k) = 1)
    (gstar : Exponent) (hgstar : gstar ∈ fullSupportGenerators (M.base.J k)) :
    ∃ (i : Fin 3) (A : ℕ), 0 < A ∧
      componentSupport M.base h C = {i} ∧
      h = A * weights M.base i ∧
      Finsupp.single i A ∈ minimalExponents (M.base.J k) := by
  classical
  obtain ⟨u, huC⟩ := C.exists_rep
  have hhK : h ∈ M.base.K := killed_mem_K M h K hkill
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
  obtain ⟨v, hvK⟩ := K.exists_rep
  have hvu : v.val ≠ u.val := by
    intro he
    apply hCK
    exact huC.symm.trans ((congrArg (fiberGraph M.base h).connectedComponentMk
      (Subtype.ext he)).symm.trans hvK)
  obtain ⟨i, hui, huoff⟩ := nonunique_minimal_border_pure k M.base hJ hJM hunique
    hq gstar u.val v.val hgstar humin (v.property.trans u.property.symm) hvu
  let A := u.val i
  have huform : u.val = Finsupp.single i A := by
    ext j
    by_cases hji : j = i
    · subst j; simp [A]
    · simp [A, hji, huoff j hji]
  have hsupp : componentSupport M.base h C = {i} := by
    ext j
    constructor
    · intro hj
      obtain ⟨w, hwC, hwj⟩ := (mem_componentSupport M.base h C j).mp hj
      have hwu' := live_component_unique_rep M h C hlive hunique w u hwC huC
      rw [hwu'] at hwj
      rw [huform] at hwj
      rw [Finset.mem_singleton]
      by_contra hji
      simpa [Finsupp.single_eq_of_ne hji] using hwj
    · intro hj
      have hji : j = i := by simpa using hj
      subst j
      exact (mem_componentSupport M.base h C i).mpr ⟨u, huC, hui⟩
  refine ⟨i, A, hui, hsupp, ?_, ?_⟩
  · calc
      h = weight M.base u.val := u.property.symm
      _ = weight M.base (Finsupp.single i A) := congrArg (weight M.base) huform
      _ = A * weights M.base i := weight_single M.base i A
  · rw [huform] at humin
    exact humin

/-- D-1 through purity: the two actual live components are singleton pure
minimal boundary gates on distinct axes. -/
theorem sectorD_live_pure_gate_data (k : Type*) [Field k]
    (P : P2Data Gamma) (hD : SectorD P.M)
    (hq : q_fs (P.M.base.J k) = 1) :
    ∃ (h g : ℕ)
      (Ch Kh : FiberComponent P.M.base h)
      (Cg Kg : FiberComponent P.M.base g)
      (ix iy : Fin 3) (A B : ℕ),
      h ≠ g ∧ 0 < h ∧ 0 < g ∧ ix ≠ iy ∧ 0 < A ∧ 0 < B ∧
      ¬ BoundaryKilled P.M h Ch ∧ BoundaryKilled P.M h Kh ∧ Ch ≠ Kh ∧
      ¬ BoundaryKilled P.M g Cg ∧ BoundaryKilled P.M g Kg ∧ Cg ≠ Kg ∧
      componentSupport P.M.base h Ch = {ix} ∧
      componentSupport P.M.base g Cg = {iy} ∧
      h = A * weights P.M.base ix ∧ g = B * weights P.M.base iy ∧
      Finsupp.single ix A ∈ minimalExponents (P.M.base.J k) ∧
      Finsupp.single iy B ∈ minimalExponents (P.M.base.J k) := by
  classical
  rcases hD with ⟨h, g, hne, hdegrees, hsigh, hsigg⟩
  change componentCount P.M.base h = 2 ∧ killedCount P.M h = 1 at hsigh
  change componentCount P.M.base g = 2 ∧ killedCount P.M g = 1 at hsigg
  have hhmem : h ∈ positiveDegrees P.M := by simp [hdegrees]
  have hgmem : g ∈ positiveDegrees P.M := by simp [hdegrees]
  have hh : 0 < h := (positive_contribution_active P.M h
    ((mem_positiveDegrees P.M h).mp hhmem)).1
  have hg : 0 < g := (positive_contribution_active P.M g
    ((mem_positiveDegrees P.M g).mp hgmem)).1
  obtain ⟨Ch, hCh, hChuniq⟩ := exactly_one_survivor P.M h (by omega)
  obtain ⟨Cg, hCg, hCguniq⟩ := exactly_one_survivor P.M g (by omega)
  have hkH : Nat.card {K : FiberComponent P.M.base h // BoundaryKilled P.M h K} = 1 :=
    hsigh.2
  have hkG : Nat.card {K : FiberComponent P.M.base g // BoundaryKilled P.M g K} = 1 :=
    hsigg.2
  obtain ⟨⟨Kh, hKh⟩, _⟩ := Nat.card_eq_one_iff_exists.mp hkH
  obtain ⟨⟨Kg, hKg⟩, _⟩ := Nat.card_eq_one_iff_exists.mp hkG
  have hChKh : Ch ≠ Kh := fun he => hCh (he ▸ hKh)
  have hCgKg : Cg ≠ Kg := fun he => hCg (he ▸ hKg)
  have hJ := sectorD_monomial k P ⟨h, g, hne, hdegrees, hsigh, hsigg⟩
  obtain ⟨hJM, hunique⟩ := sectorD_boundary_payload k P
    ⟨h, g, hne, hdegrees, hsigh, hsigg⟩
  rw [q_fs] at hq
  obtain ⟨gstar, hgset⟩ := Set.ncard_eq_one.mp hq
  have hgstar : gstar ∈ fullSupportGenerators (P.M.base.J k) := by simp [hgset]
  have hq' : q_fs (P.M.base.J k) = 1 := by rw [q_fs, hgset]; simp
  obtain ⟨ix, A, hA, hsCh, hAh, huA⟩ := live_component_minimal_pure_gate
    k P.M h Ch Kh hCh hKh hChKh hJ hJM hunique hq' gstar hgstar
  obtain ⟨iy, B, hB, hsCg, hBg, huB⟩ := live_component_minimal_pure_gate
    k P.M g Cg Kg hCg hKg hCgKg hJ hJM hunique hq' gstar hgstar
  have hxy : ix ≠ iy := by
    intro he
    have hsCg' : componentSupport P.M.base g Cg = {ix} := by simpa [he] using hsCg
    have hge := singleton_active_degree_unique P.M.base h g hh hg (by omega) (by omega)
      Ch Cg ix hsCh hsCg'
    exact hne hge
  exact ⟨h, g, Ch, Kh, Cg, Kg, ix, iy, A, B, hne, hh, hg, hxy, hA, hB,
    hCh, hKh, hChKh, hCg, hKg, hCgKg, hsCh, hsCg, hAh, hBg, huA, huB⟩

private theorem third_axis_exists (ix iy : Fin 3) (hxy : ix ≠ iy) :
    ∃ iz : Fin 3, iz ≠ ix ∧ iz ≠ iy := by
  fin_cases ix <;> fin_cases iy <;> simp_all <;>
    first | exact ⟨0, by decide, by decide⟩
          | exact ⟨1, by decide, by decide⟩
          | exact ⟨2, by decide, by decide⟩

private theorem fin3_eq_one_of_axes (ix iy iz j : Fin 3)
    (hxy : ix ≠ iy) (hzx : iz ≠ ix) (hzy : iz ≠ iy) :
    j = ix ∨ j = iy ∨ j = iz := by
  fin_cases ix <;> fin_cases iy <;> fin_cases iz <;> fin_cases j <;> simp_all

private theorem exponent_three_axes (ix iy iz : Fin 3)
    (hxy : ix ≠ iy) (hzx : iz ≠ ix) (hzy : iz ≠ iy) (u : Exponent) :
    u = Finsupp.single ix (u ix) + Finsupp.single iy (u iy) +
      Finsupp.single iz (u iz) := by
  ext j
  rcases fin3_eq_one_of_axes ix iy iz j hxy hzx hzy with rfl | rfl | rfl
  · simp [hxy, Ne.symm hzx]
  · simp [Ne.symm hxy, Ne.symm hzy]
  · simp [hzx, hzy]

/-- D-1 gate geometry, obtained from actual killed-component representatives.
The transverse coefficients are minimized before the audited substitution
argument; no equation or inequality is assumed. -/
theorem sectorD_gate_geometry (k : Type*) [Field k]
    (P : P2Data Gamma) (hD : SectorD P.M)
    (hq : q_fs (P.M.base.J k) = 1) :
    ∃ (ix iy iz : Fin 3) (A B lambda mu nu omega : ℕ),
      ix ≠ iy ∧ iz ≠ ix ∧ iz ≠ iy ∧ 0 < A ∧ 0 < B ∧
      A * weights P.M.base ix = lambda * weights P.M.base iy + mu * weights P.M.base iz ∧
      B * weights P.M.base iy = nu * weights P.M.base ix + omega * weights P.M.base iz ∧
      lambda < B ∧ nu < A ∧ 0 < mu ∧ 0 < omega ∧
      Finsupp.single ix A ∈ minimalExponents (P.M.base.J k) ∧
      Finsupp.single iy B ∈ minimalExponents (P.M.base.J k) := by
  classical
  obtain ⟨h, g, Ch, Kh, Cg, Kg, ix, iy, A, B, hne, hh, hg, hxy, hA, hB,
    hCh, hKh, hChKh, hCg, hKg, hCgKg, hsCh, hsCg, hAh, hBg, huA, huB⟩ :=
    sectorD_live_pure_gate_data k P hD hq
  obtain ⟨iz, hzx, hzy⟩ := third_axis_exists ix iy hxy
  obtain ⟨vh0, hvhK⟩ := Kh.exists_rep
  obtain ⟨vg0, hvgK⟩ := Kg.exists_rep
  have hvhix : vh0.val ix = 0 := by
    by_contra hn
    have hxK : ix ∈ componentSupport P.M.base h Kh :=
      (mem_componentSupport P.M.base h Kh ix).mpr ⟨vh0, hvhK, Nat.pos_of_ne_zero hn⟩
    have hxC : ix ∈ componentSupport P.M.base h Ch := by simp [hsCh]
    exact hChKh (components_eq_of_shared_support P.M.base h Ch Kh ix hxC hxK)
  have hvgiy : vg0.val iy = 0 := by
    by_contra hn
    have hyK : iy ∈ componentSupport P.M.base g Kg :=
      (mem_componentSupport P.M.base g Kg iy).mpr ⟨vg0, hvgK, Nat.pos_of_ne_zero hn⟩
    have hyC : iy ∈ componentSupport P.M.base g Cg := by simp [hsCg]
    exact hCgKg (components_eq_of_shared_support P.M.base g Cg Kg iy hyC hyK)
  have hexH : ∃ l : ℕ, ∃ v : FactorizationFiber P.M.base h,
      v.val ix = 0 ∧ v.val iy = l := ⟨vh0.val iy, vh0, hvhix, rfl⟩
  have hexG : ∃ n : ℕ, ∃ v : FactorizationFiber P.M.base g,
      v.val iy = 0 ∧ v.val ix = n := ⟨vg0.val ix, vg0, hvgiy, rfl⟩
  let lambda := Nat.find hexH
  let nu := Nat.find hexG
  obtain ⟨vh, hvhix', hvhiy⟩ := Nat.find_spec hexH
  obtain ⟨vg, hvgiy', hvgix⟩ := Nat.find_spec hexG
  let mu := vh.val iz
  let omega := vg.val iz
  have hvhform : vh.val = Finsupp.single iy lambda + Finsupp.single iz mu := by
    rw [exponent_three_axes ix iy iz hxy hzx hzy vh.val]
    simp [hvhix', hvhiy, lambda, mu]
  have hvgform : vg.val = Finsupp.single ix nu + Finsupp.single iz omega := by
    rw [exponent_three_axes ix iy iz hxy hzx hzy vg.val]
    simp [hvgiy', hvgix, nu, omega]
  have hgate1 : A * weights P.M.base ix =
      lambda * weights P.M.base iy + mu * weights P.M.base iz := by
    rw [← hAh, ← vh.property, hvhform, map_add, weight_single, weight_single]
  have hgate2 : B * weights P.M.base iy =
      nu * weights P.M.base ix + omega * weights P.M.base iz := by
    rw [← hBg, ← vg.property, hvgform, map_add, weight_single, weight_single]
  obtain ⟨hJM, hunique⟩ := sectorD_boundary_payload k P hD
  let ux : FactorizationFiber P.M.base h := ⟨Finsupp.single ix A, by
    rw [weight_single, ← hAh]⟩
  let uy : FactorizationFiber P.M.base g := ⟨Finsupp.single iy B, by
    rw [weight_single, ← hBg]⟩
  have huxC : (fiberGraph P.M.base h).connectedComponentMk ux = Ch := by
    apply components_eq_of_shared_support P.M.base h _ Ch ix
    · apply (mem_componentSupport P.M.base h _ ix).mpr
      exact ⟨ux, rfl, by simp [ux, hA]⟩
    · simp [hsCh]
  have huyC : (fiberGraph P.M.base g).connectedComponentMk uy = Cg := by
    apply components_eq_of_shared_support P.M.base g _ Cg iy
    · apply (mem_componentSupport P.M.base g _ iy).mpr
      exact ⟨uy, rfl, by simp [uy, hB]⟩
    · simp [hsCg]
  have hlambda : lambda < B := by
    by_contra hn
    have hBl : B ≤ lambda := by omega
    let wval := (vh.val - Finsupp.single iy B) + vg.val
    have hwweight : weight P.M.base wval = h := by
      simp only [wval, map_add]
      have hvhrem : weight P.M.base (vh.val - Finsupp.single iy B) =
          (lambda - B) * weights P.M.base iy + mu * weights P.M.base iz := by
        have hvhsub : vh.val - Finsupp.single iy B =
            Finsupp.single iy (lambda - B) + Finsupp.single iz mu := by
          rw [hvhform]
          ext j
          rcases fin3_eq_one_of_axes ix iy iz j hxy hzx hzy with rfl | rfl | rfl
          · simp [hxy, Ne.symm hzx]
          · simp [Ne.symm hxy, Ne.symm hzy]
          · simp [hzx, hzy]
        rw [hvhsub, map_add, weight_single, weight_single]
      rw [hvhrem, vg.property, hBg]
      calc
        (lambda - B) * weights P.M.base iy + mu * weights P.M.base iz +
            B * weights P.M.base iy =
            ((lambda - B) + B) * weights P.M.base iy +
              mu * weights P.M.base iz := by ring
        _ = lambda * weights P.M.base iy + mu * weights P.M.base iz := by
          rw [Nat.sub_add_cancel hBl]
        _ = A * weights P.M.base ix := hgate1.symm
        _ = h := hAh.symm
    let w : FactorizationFiber P.M.base h := ⟨wval, hwweight⟩
    have hwix : w.val ix = nu := by simp [w, wval, hvhform, hvgform, hxy, hzx]
    have hwiy : w.val iy = lambda - B := by
      simp [w, wval, hvhform, hvgform, hxy, hzy]
    have hwiz : w.val iz = mu + omega := by
      simp [w, wval, hvhform, hvgform, hzx, hzy]
    by_cases hnu : nu = 0
    · have hmin := Nat.find_min' hexH ⟨w, by simpa [hwix, hnu], hwiy⟩
      omega
    · have hnupos : 0 < nu := Nat.pos_of_ne_zero hnu
      have hwC : (fiberGraph P.M.base h).connectedComponentMk w = Ch := by
        by_cases he : w = ux
        · simpa [he] using huxC
        · have ha : (fiberGraph P.M.base h).Adj w ux := by
            refine ⟨he, ix, ?_, ?_⟩
            · simpa [hwix] using hnupos
            · simp [ux, hA]
          exact (SimpleGraph.ConnectedComponent.sound ha.reachable).trans huxC
      have he := congrArg Subtype.val
        (live_component_unique_rep P.M h Ch hCh hunique w ux hwC huxC)
      have heix := congrArg (fun z : Exponent => z ix) he
      have heiy := congrArg (fun z : Exponent => z iy) he
      have heiz := congrArg (fun z : Exponent => z iz) he
      simp [w, ux, hwix, hwiy, hwiz, hxy, hzx, hzy] at heix heiy heiz
      have hmu0 : mu = 0 := by omega
      have homega0 : omega = 0 := by omega
      have hlB : lambda = B := by omega
      apply hne
      rw [hAh, hgate1, hlB, hmu0, zero_mul, add_zero, ← hBg]
  have hnuA : nu < A := by
    by_contra hn
    have hAn : A ≤ nu := by omega
    let wval := (vg.val - Finsupp.single ix A) + vh.val
    have hwweight : weight P.M.base wval = g := by
      simp only [wval, map_add]
      have hvgrem : weight P.M.base (vg.val - Finsupp.single ix A) =
          (nu - A) * weights P.M.base ix + omega * weights P.M.base iz := by
        have hvgsub : vg.val - Finsupp.single ix A =
            Finsupp.single ix (nu - A) + Finsupp.single iz omega := by
          rw [hvgform]
          ext j
          rcases fin3_eq_one_of_axes ix iy iz j hxy hzx hzy with rfl | rfl | rfl
          · simp [hxy, hzx]
          · simp [Ne.symm hxy, Ne.symm hzy]
          · simp [hzx, hzy]
        rw [hvgsub, map_add, weight_single, weight_single]
      rw [hvgrem, vh.property, hAh]
      calc
        (nu - A) * weights P.M.base ix + omega * weights P.M.base iz +
            A * weights P.M.base ix =
            ((nu - A) + A) * weights P.M.base ix +
              omega * weights P.M.base iz := by ring
        _ = nu * weights P.M.base ix + omega * weights P.M.base iz := by
          rw [Nat.sub_add_cancel hAn]
        _ = B * weights P.M.base iy := hgate2.symm
        _ = g := hBg.symm
    let w : FactorizationFiber P.M.base g := ⟨wval, hwweight⟩
    have hwiy : w.val iy = lambda := by simp [w, wval, hvhform, hvgform, hxy, hzy]
    have hwix : w.val ix = nu - A := by simp [w, wval, hvhform, hvgform, hxy, hzx]
    have hwiz : w.val iz = omega + mu := by simp [w, wval, hvhform, hvgform, hzx, hzy]
    by_cases hlam : lambda = 0
    · have hmin := Nat.find_min' hexG ⟨w, by simpa [hwiy, hlam], hwix⟩
      omega
    · have hlampos : 0 < lambda := Nat.pos_of_ne_zero hlam
      have hwC : (fiberGraph P.M.base g).connectedComponentMk w = Cg := by
        by_cases he : w = uy
        · simpa [he] using huyC
        · have ha : (fiberGraph P.M.base g).Adj w uy := by
            refine ⟨he, iy, ?_, ?_⟩
            · simpa [hwiy] using hlampos
            · simp [uy, hB]
          exact (SimpleGraph.ConnectedComponent.sound ha.reachable).trans huyC
      have he := congrArg Subtype.val
        (live_component_unique_rep P.M g Cg hCg hunique w uy hwC huyC)
      have heix := congrArg (fun z : Exponent => z ix) he
      have heiy := congrArg (fun z : Exponent => z iy) he
      have heiz := congrArg (fun z : Exponent => z iz) he
      simp [w, uy, hwix, hwiy, hwiz, hxy, hzx, hzy] at heix heiy heiz
      have hmu0 : mu = 0 := by omega
      have homega0 : omega = 0 := by omega
      have hnA : nu = A := by omega
      have hlB : lambda = B := heiy
      apply hne
      calc
        h = A * weights P.M.base ix := hAh
        _ = lambda * weights P.M.base iy + mu * weights P.M.base iz := hgate1
        _ = B * weights P.M.base iy := by rw [hlB, hmu0]; simp
        _ = g := hBg.symm
  have hmu : 0 < mu := by
    by_contra hn
    have hmu0 : mu = 0 := by omega
    have hvhEq : vh.val = Finsupp.single iy lambda := by simp [hvhform, hmu0]
    have hhK : h ∈ P.M.base.K := killed_mem_K P.M h Kh hKh
    have hvhJ : MvPolynomial.monomial vh.val (1 : k) ∈ P.M.base.J k :=
      boundary_monomial_mem_J k P.M.base vh.val (vh.property.symm ▸ hhK)
    have hvhle : vh.val ≤ Finsupp.single iy B := by
      rw [hvhEq]
      intro j
      by_cases hji : j = iy
      · subst j; simp; omega
      · simp [hji]
    have hle := huB.2 hvhJ hvhle
    have := hle iy
    simp [hvhEq] at this
    omega
  have homega : 0 < omega := by
    by_contra hn
    have homega0 : omega = 0 := by omega
    have hvgEq : vg.val = Finsupp.single ix nu := by simp [hvgform, homega0]
    have hgK : g ∈ P.M.base.K := killed_mem_K P.M g Kg hKg
    have hvgJ : MvPolynomial.monomial vg.val (1 : k) ∈ P.M.base.J k :=
      boundary_monomial_mem_J k P.M.base vg.val (vg.property.symm ▸ hgK)
    have hvgle : vg.val ≤ Finsupp.single ix A := by
      rw [hvgEq]
      intro j
      by_cases hji : j = ix
      · subst j; simp; omega
      · simp [hji]
    have hle := huA.2 hvgJ hvgle
    have := hle ix
    simp [hvgEq] at this
    omega
  exact ⟨ix, iy, iz, A, B, lambda, mu, nu, omega, hxy, hzx, hzy, hA, hB,
    hgate1, hgate2, hlambda, hnuA, hmu, homega, huA, huB⟩

set_option maxHeartbeats 800000 in
private theorem one_gate_reaches_third_axis (k : Type*) [Field k]
    (P : P2Data Gamma) (hJ : IsMonomialIdeal k (P.M.base.J k))
    (hJM : P.M.base.J k = P.M.base.MK k)
    (hunique : ∀ d, d ∈ P.M.base.apery → Subsingleton (FactorizationFiber P.M.base d))
    (hq : q_fs (P.M.base.J k) = 1)
    (ix iy iz : Fin 3) (A B C lambda mu : ℕ)
    (hxy : ix ≠ iy) (hzx : iz ≠ ix) (hzy : iz ≠ iy)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hgate : A * weights P.M.base ix =
      lambda * weights P.M.base iy + mu * weights P.M.base iz)
    (hlambda : lambda < B) (hmu : 0 < mu)
    (huA : Finsupp.single ix A ∈ minimalExponents (P.M.base.J k))
    (huB : Finsupp.single iy B ∈ minimalExponents (P.M.base.J k))
    (huC : Finsupp.single iz C ∈ minimalExponents (P.M.base.J k)) :
    C ≤ mu := by
  classical
  rw [q_fs] at hq
  obtain ⟨g, hgset⟩ := Set.ncard_eq_one.mp hq
  have hg : g ∈ fullSupportGenerators (P.M.base.J k) := by simp [hgset]
  let u : Exponent := Finsupp.single ix A
  have hug : u ≠ g := by
    intro he
    have hgy := hg.2 iy
    rw [← he] at hgy
    simp [u, Ne.symm hxy] at hgy
  have huA' : u ∈ minimalExponents (P.M.base.J k) := by simpa [u] using huA
  obtain ⟨r, ell, _hrA, hdepth, hsupport, hell, helllt, _hrne⟩ :=
    minimal_boundary_depth k P.M.base hJ hJM hunique g u hg huA' hug
  have huix : 0 < u ix := by simpa [u] using hA
  have hrix : r ix = 0 := hsupport ix huix
  have hrform : r = Finsupp.single iy (r iy) + Finsupp.single iz (r iz) := by
    calc
      r = Finsupp.single ix (r ix) + Finsupp.single iy (r iy) +
          Finsupp.single iz (r iz) := exponent_three_axes ix iy iz hxy hzx hzy r
      _ = Finsupp.single iy (r iy) + Finsupp.single iz (r iz) := by rw [hrix]; simp
  have hdepth' : A * weights P.M.base ix =
      r iy * weights P.M.base iy + r iz * weights P.M.base iz +
        ell * P.M.base.q.val := by
    have hwr := congrArg (weight P.M.base) hrform
    simp only [map_add, weight_single] at hwr
    calc
      A * weights P.M.base ix = weight P.M.base r + ell * P.M.base.q.val := by
        simpa [u, weight_single] using hdepth
      _ = r iy * weights P.M.base iy + r iz * weights P.M.base iz +
          ell * P.M.base.q.val := by rw [hwr]
  have hellq : 0 < ell * P.M.base.q.val := Nat.mul_pos hell P.M.base.q_positive
  have hriy : lambda < r iy := by
    by_contra hn
    have hryle : r iy ≤ lambda := by omega
    by_cases hrzle : r iz ≤ mu
    · let rem : Exponent := Finsupp.single iy (lambda - r iy) +
          Finsupp.single iz (mu - r iz)
      have hdiff : weight P.M.base rem = ell * P.M.base.q.val := by
        have hly := Nat.sub_add_cancel hryle
        have hmz := Nat.sub_add_cancel hrzle
        simp only [rem, map_add, weight_single]
        nlinarith
      have hreturn : ell * P.M.base.q.val ∈ P.M.base.H := by
        rw [← hdiff]
        exact weight_mem_H P.M.base rem
      have hmin := firstReturnMultiplier_minimal P.M.base hell hreturn
      omega
    · have hmurz : mu < r iz := by omega
      let pred : Exponent := Finsupp.single iy (lambda - r iy)
      let rem : Exponent := Finsupp.single iz (r iz - mu)
      have hcoef : 0 < lambda - r iy := by
        have hly := Nat.sub_add_cancel hryle
        have hz := Nat.sub_add_cancel hmurz.le
        nlinarith [hgate, hdepth', hellq, weights_positive P.M.base iz]
      have heq : weight P.M.base pred =
          weight P.M.base rem + ell * P.M.base.q.val := by
        have hly := Nat.sub_add_cancel hryle
        have hmz := Nat.sub_add_cancel hmurz.le
        simp only [pred, rem, weight_single]
        nlinarith
      have hpredK : weight P.M.base pred ∈ P.M.base.K :=
        degree_in_K_of_positive_pivot P.M.base pred (weight P.M.base rem) ell
          (P.M.base.H_le (weight_mem_H P.M.base rem)) hell heq
      have hpredJ : MvPolynomial.monomial pred (1 : k) ∈ P.M.base.J k :=
        boundary_monomial_mem_J k P.M.base pred hpredK
      have hpredle : pred ≤ Finsupp.single iy B := by
        intro j
        by_cases hji : j = iy
        · subst j; simp [pred]; omega
        · simp [pred, hji]
      have hminle := huB.2 hpredJ hpredle
      have := hminle iy
      simp [pred] at this
      omega
  have hriz : r iz < mu := by
    by_contra hn
    have hmule : mu ≤ r iz := by omega
    have hrypos : 0 < r iy - lambda := Nat.sub_pos_of_lt hriy
    have hrz := Nat.sub_add_cancel hmule
    have hry := Nat.sub_add_cancel hriy.le
    nlinarith [weights_positive P.M.base iy]
  let pred : Exponent := Finsupp.single iz (mu - r iz)
  let rem : Exponent := Finsupp.single iy (r iy - lambda)
  have heq : weight P.M.base pred =
      weight P.M.base rem + ell * P.M.base.q.val := by
    have hry := Nat.sub_add_cancel hriy.le
    have hmz := Nat.sub_add_cancel hriz.le
    simp only [pred, rem, weight_single]
    nlinarith
  have hpredK : weight P.M.base pred ∈ P.M.base.K :=
    degree_in_K_of_positive_pivot P.M.base pred (weight P.M.base rem) ell
      (P.M.base.H_le (weight_mem_H P.M.base rem)) hell heq
  have hpredJ : MvPolynomial.monomial pred (1 : k) ∈ P.M.base.J k :=
    boundary_monomial_mem_J k P.M.base pred hpredK
  by_contra hn
  have hcoeflt : mu - r iz < C := by omega
  have hpredle : pred ≤ Finsupp.single iz C := by
    intro j
    by_cases hji : j = iz
    · subst j; simpa [pred] using hcoeflt.le
    · simp [pred, hji]
  have hminle := huC.2 hpredJ hpredle
  have hc := hminle iz
  simp [pred] at hc
  omega

/-- D-2.  The Artinian third-axis boundary and both domination inequalities
are constructed from the actual gates; none is supplied as a premise. -/
theorem sectorD_gate_domination (k : Type*) [Field k]
    (P : P2Data Gamma) (hD : SectorD P.M)
    (hq : q_fs (P.M.base.J k) = 1) :
    ∃ (ix iy iz : Fin 3) (A B C lambda mu nu omega : ℕ),
      ix ≠ iy ∧ iz ≠ ix ∧ iz ≠ iy ∧ 0 < A ∧ 0 < B ∧ 0 < C ∧
      A * weights P.M.base ix = lambda * weights P.M.base iy + mu * weights P.M.base iz ∧
      B * weights P.M.base iy = nu * weights P.M.base ix + omega * weights P.M.base iz ∧
      lambda < B ∧ nu < A ∧ 0 < mu ∧ 0 < omega ∧ C ≤ mu ∧ C ≤ omega ∧
      Finsupp.single ix A ∈ minimalExponents (P.M.base.J k) ∧
      Finsupp.single iy B ∈ minimalExponents (P.M.base.J k) ∧
      Finsupp.single iz C ∈ minimalExponents (P.M.base.J k) := by
  classical
  obtain ⟨ix, iy, iz, A, B, lambda, mu, nu, omega, hxy, hzx, hzy, hA, hB,
    hgate1, hgate2, hlB, hnA, hmu, homega, huA, huB⟩ :=
    sectorD_gate_geometry k P hD hq
  have hJ := sectorD_monomial k P hD
  obtain ⟨hJM, hunique⟩ := sectorD_boundary_payload k P hD
  let Art := chosenArtinianMonomial P.M.base MonomialOrder.degLex hJ
  obtain ⟨uz, huz, huzpos, huzoff⟩ := L3A.Staircase.pure_minimal Art iz
  let C := uz iz
  have huzform : uz = Finsupp.single iz C := by
    ext j
    by_cases hji : j = iz
    · subst j; simp [C]
    · simp [hji, huzoff j hji]
  have hC : 0 < C := by simpa [C] using huzpos
  have huC : Finsupp.single iz C ∈ minimalExponents (P.M.base.J k) := by
    change uz ∈ minimalExponents (P.M.base.J k) at huz
    rwa [huzform] at huz
  have hCmu := one_gate_reaches_third_axis k P hJ hJM hunique hq
    ix iy iz A B C lambda mu hxy hzx hzy hA hB hC hgate1 hlB hmu huA huB huC
  have hComega := one_gate_reaches_third_axis k P hJ hJM hunique hq
    iy ix iz B A C nu omega (Ne.symm hxy) hzy hzx hB hA hC hgate2 hnA homega
      huB huA huC
  exact ⟨ix, iy, iz, A, B, C, lambda, mu, nu, omega, hxy, hzx, hzy, hA, hB,
    hC, hgate1, hgate2, hlB, hnA, hmu, homega, hCmu, hComega, huA, huB, huC⟩

set_option maxHeartbeats 800000 in
/-- D-3.  DEPTH for the actual third-axis boundary is incompatible with the
two dominated live gates. -/
theorem sectorD_q_fs_one_impossible (k : Type*) [Field k]
    (P : P2Data Gamma) (hD : SectorD P.M) :
    q_fs (P.M.base.J k) = 1 → False := by
  classical
  intro hq
  obtain ⟨ix, iy, iz, A, B, C, lambda, mu, nu, omega, hxy, hzx, hzy, hA, hB,
    hC, hgate1, hgate2, hlB, hnA, hmu, homega, hCmu, hComega, huA, huB, huC⟩ :=
    sectorD_gate_domination k P hD hq
  have hJ := sectorD_monomial k P hD
  obtain ⟨hJM, hunique⟩ := sectorD_boundary_payload k P hD
  rw [q_fs] at hq
  obtain ⟨g, hgset⟩ := Set.ncard_eq_one.mp hq
  have hg : g ∈ fullSupportGenerators (P.M.base.J k) := by simp [hgset]
  let u : Exponent := Finsupp.single iz C
  have hug : u ≠ g := by
    intro he
    have hgx := hg.2 ix
    rw [← he] at hgx
    simp [u, hzx] at hgx
  have huC' : u ∈ minimalExponents (P.M.base.J k) := by simpa [u] using huC
  obtain ⟨r, ell, _hrA, hdepth, hsupport, hell, _helllt, hrne⟩ :=
    minimal_boundary_depth k P.M.base hJ hJM hunique g u hg huC' hug
  have huiz : 0 < u iz := by simpa [u] using hC
  have hriz : r iz = 0 := hsupport iz huiz
  have hrform : r = Finsupp.single ix (r ix) + Finsupp.single iy (r iy) := by
    calc
      r = Finsupp.single ix (r ix) + Finsupp.single iy (r iy) +
          Finsupp.single iz (r iz) := exponent_three_axes ix iy iz hxy hzx hzy r
      _ = Finsupp.single ix (r ix) + Finsupp.single iy (r iy) := by rw [hriz]; simp
  have hdepth' : C * weights P.M.base iz =
      r ix * weights P.M.base ix + r iy * weights P.M.base iy +
        ell * P.M.base.q.val := by
    have hwr := congrArg (weight P.M.base) hrform
    simp only [map_add, weight_single] at hwr
    calc
      C * weights P.M.base iz = weight P.M.base r + ell * P.M.base.q.val := by
        simpa [u, weight_single] using hdepth
      _ = r ix * weights P.M.base ix + r iy * weights P.M.base iy +
          ell * P.M.base.q.val := by rw [hwr]
  have hrix : r ix = 0 := by
    by_contra hn
    have hrixpos : 0 < r ix := Nat.pos_of_ne_zero hn
    let pred : Exponent := Finsupp.single ix (A - 1)
    let rem : Exponent := Finsupp.single ix (r ix - 1) +
      Finsupp.single iy (lambda + r iy) + Finsupp.single iz (mu - C)
    have hAone := Nat.sub_add_cancel hA
    have hrone := Nat.sub_add_cancel hrixpos
    have hmC := Nat.sub_add_cancel hCmu
    have heq : weight P.M.base pred =
        weight P.M.base rem + ell * P.M.base.q.val := by
      simp only [pred, rem, map_add, weight_single]
      nlinarith
    have hpredK : weight P.M.base pred ∈ P.M.base.K :=
      degree_in_K_of_positive_pivot P.M.base pred (weight P.M.base rem) ell
        (P.M.base.H_le (weight_mem_H P.M.base rem)) hell heq
    have hap := minimal_boundary_remove_apery k P.M.base hJM
      (Finsupp.single ix A) huA ix (by simpa using hA)
    have hpredEq : weight P.M.base pred =
        weight P.M.base (Finsupp.single ix A) - weights P.M.base ix := by
      simp only [pred, weight_single]
      rw [Nat.sub_mul]
      simp
    exact (P.M.base.apery_eq_compl ▸ hap).2 (hpredEq ▸ hpredK)
  have hriy : r iy = 0 := by
    by_contra hn
    have hriypos : 0 < r iy := Nat.pos_of_ne_zero hn
    let pred : Exponent := Finsupp.single iy (B - 1)
    let rem : Exponent := Finsupp.single ix (nu + r ix) +
      Finsupp.single iy (r iy - 1) + Finsupp.single iz (omega - C)
    have hBone := Nat.sub_add_cancel hB
    have hrone := Nat.sub_add_cancel hriypos
    have hoC := Nat.sub_add_cancel hComega
    have heq : weight P.M.base pred =
        weight P.M.base rem + ell * P.M.base.q.val := by
      simp only [pred, rem, map_add, weight_single]
      nlinarith
    have hpredK : weight P.M.base pred ∈ P.M.base.K :=
      degree_in_K_of_positive_pivot P.M.base pred (weight P.M.base rem) ell
        (P.M.base.H_le (weight_mem_H P.M.base rem)) hell heq
    have hap := minimal_boundary_remove_apery k P.M.base hJM
      (Finsupp.single iy B) huB iy (by simpa using hB)
    have hpredEq : weight P.M.base pred =
        weight P.M.base (Finsupp.single iy B) - weights P.M.base iy := by
      simp only [pred, weight_single]
      rw [Nat.sub_mul]
      simp
    exact (P.M.base.apery_eq_compl ▸ hap).2 (hpredEq ▸ hpredK)
  apply hrne
  ext j
  rcases fin3_eq_one_of_axes ix iy iz j hxy hzx hzy with rfl | rfl | rfl
  · exact hrix
  · exact hriy
  · exact hriz

/-- D-4.  Unconditional Sector-D endpoint closure. -/
theorem sectorD_target (k : Type*) [Field k]
    (P : P2Data Gamma) (hD : SectorD P.M) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  rcases sectorD_q_fs_dichotomy k P hD with hq | hq
  · exact sectorD_target_of_q_fs_zero k P hD hq
  · exact (sectorD_q_fs_one_impossible k P hD hq).elim

/-- Exact original Sector D binder, with the coefficient field chosen internally. -/
theorem sectorD_type_le_sourceCount (P : P2Data Gamma) (hD : SectorD P.M) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount :=
  sectorD_target ℚ P hD

end NS25Lean.L5A2R49D


