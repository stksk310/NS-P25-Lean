import NS25Lean.P2SectorCT10BoundaryCorrectionR27

set_option linter.style.header false
set_option linter.style.haveILetI false
set_option linter.style.whitespace false
noncomputable section

namespace NS25Lean.L5A2C4OR29

open L2B L5A1 L5A2C3G L5A2C4A L5A2C4B L5A2C4C L5A2C4D
  L5A2C4H L5A2C4OR1 L5A2C4OR3 L5A2C4OR5 L5A2C4OR19
  L5A2C4OR22 FourGeneratedBridge

variable {Gamma : NumericalSemigroup}

/-- The model uses the literal overlap graph, not a declared graph signature. -/
theorem actual_fiber_adjacency (B : ChosenBase.Data Gamma) (h : ℕ)
    (u v : FactorizationFiber B h) :
    (fiberGraph B h).Adj u v ↔ u ≠ v ∧ ∃ j, 0 < u.val j ∧ 0 < v.val j := Iff.rfl

/-- Union support, rather than the support of a chosen normal monomial. -/
theorem killed_iff_support_predecessor (M : MultiplicityBase Gamma) (h : ℕ)
    (C : FiberComponent M.base h) :
    BoundaryKilled M h C ↔
      ∃ j ∈ componentSupport M.base h C, h - weights M.base j ∈ M.base.K := by
  constructor
  · rintro ⟨u, hu, j, hj, hk⟩
    exact ⟨j, (mem_componentSupport _ _ _ _).mpr ⟨u, hu, hj⟩, hk⟩
  · rintro ⟨j, hj, hk⟩
    obtain ⟨u, hu, hj⟩ := (mem_componentSupport _ _ _ _).mp hj
    exact ⟨u, hu, j, hj, hk⟩

theorem killed_iff_singleton_predecessor (M : MultiplicityBase Gamma) (h : ℕ)
    (C : FiberComponent M.base h) (j : Fin 3)
    (hs : componentSupport M.base h C = {j}) :
    BoundaryKilled M h C ↔ h - weights M.base j ∈ M.base.K := by
  rw [killed_iff_support_predecessor, hs]
  simp

theorem killed_iff_pair_predecessor (M : MultiplicityBase Gamma) (h : ℕ)
    (C : FiberComponent M.base h) (j k : Fin 3)
    (hs : componentSupport M.base h C = {j, k}) :
    BoundaryKilled M h C ↔
      h - weights M.base j ∈ M.base.K ∨ h - weights M.base k ∈ M.base.K := by
  rw [killed_iff_support_predecessor, hs]
  simp

theorem all_killed_of_count_eq (M : MultiplicityBase Gamma) (h : ℕ)
    (hk : killedCount M h = componentCount M.base h) :
    ∀ C : FiberComponent M.base h, BoundaryKilled M h C := by
  classical
  letI := Fintype.ofFinite (FiberComponent M.base h)
  letI := Fintype.ofFinite {C : FiberComponent M.base h // BoundaryKilled M h C}
  have hc : Fintype.card {C : FiberComponent M.base h // BoundaryKilled M h C} =
      Fintype.card (FiberComponent M.base h) := by
    simpa only [killedCount, componentCount, Nat.card_eq_fintype_card] using hk
  have hs := ((Fintype.bijective_iff_injective_and_card
    (Subtype.val : {C : FiberComponent M.base h // BoundaryKilled M h C} →
      FiberComponent M.base h)).mpr ⟨Subtype.val_injective, hc⟩).2
  intro C
  obtain ⟨D, hD⟩ := hs C
  simpa only [hD] using D.property

theorem none_killed_of_count_zero (M : MultiplicityBase Gamma) (h : ℕ)
    (hk : killedCount M h = 0) (C : FiberComponent M.base h) : ¬BoundaryKilled M h C := by
  intro hC
  have hp : 0 < killedCount M h :=
    Nat.card_pos_iff.mpr ⟨⟨⟨C, hC⟩⟩, inferInstance⟩
  omega

/-- The same caller-supplied R, with no DirectPF/notch/orientation premise. -/
theorem actual_critical_role_degrees {P : P2Data Gamma} (R : ActualRolePacket P) :
    R.G.internalDegree = c2 P.M.base R.e * weights P.M.base (R.e 1) ∧
      R.G.boundaryDegree = c3 P.M.base R.e * weights P.M.base (R.e 2) :=
  actual_internal_boundary_critical_degrees R.G R.e R.internalPure R.boundaryPure
    R.pureB R.pureC

theorem actual_inactive_predecessors {P : P2Data Gamma} (R : ActualRolePacket P) :
    let h := c1 P.M.base R.e * weights P.M.base (R.e 0)
    h - weights P.M.base (R.e 0) ∈ P.M.base.K ∧
      (h - weights P.M.base (R.e 1) ∈ P.M.base.K ∨
       h - weights P.M.base (R.e 2) ∈ P.M.base.K) := by
  dsimp only
  have hall := all_killed_of_count_eq P.M _ (R.inactive.2.trans R.inactive.1.symm)
  constructor
  · exact (killed_iff_singleton_predecessor P.M _
      (critical_pure_component P.M.base (R.e 0)) (R.e 0)
      (critical_component_support_eq_singleton _ _)).mp (hall _)
  · obtain ⟨C, _, hs⟩ := exists_h1_nonpure_component_support R.G R.e
      R.internalPure R.internalMixed R.boundaryPure R.boundaryMixed
      R.internal_ne R.boundary_ne R.pureB R.mixedAC R.pureC R.mixedAB
    exact (killed_iff_pair_predecessor P.M _ C (R.e 1) (R.e 2) hs).mp (hall C)

theorem actual_internal_predecessors_live {P : P2Data Gamma} (R : ActualRolePacket P) :
    R.G.internalDegree - weights P.M.base (R.e 0) ∉ P.M.base.K ∧
    R.G.internalDegree - weights P.M.base (R.e 1) ∉ P.M.base.K ∧
    R.G.internalDegree - weights P.M.base (R.e 2) ∉ P.M.base.K := by
  have hp := none_killed_of_count_zero P.M _ R.G.internalSignature.2 R.internalPure
  have hm := none_killed_of_count_zero P.M _ R.G.internalSignature.2 R.internalMixed
  rw [killed_iff_singleton_predecessor _ _ _ _ R.pureB] at hp
  rw [killed_iff_pair_predecessor _ _ _ _ _ R.mixedAC] at hm
  exact ⟨fun h => hm (Or.inl h), hp, fun h => hm (Or.inr h)⟩

theorem actual_boundary_predecessor_dichotomy {P : P2Data Gamma}
    (R : ActualRolePacket P) :
    let h := R.G.boundaryDegree
    let a := weights P.M.base (R.e 0)
    let b := weights P.M.base (R.e 1)
    let c := weights P.M.base (R.e 2)
    ((h-c ∈ P.M.base.K) ∧ (h-a ∉ P.M.base.K) ∧ (h-b ∉ P.M.base.K)) ∨
      ((h-c ∉ P.M.base.K) ∧ (h-a ∈ P.M.base.K ∨ h-b ∈ P.M.base.K)) := by
  dsimp only
  have hall : ∀ E : boundaryComponents R.G, E = R.boundaryPure ∨ E = R.boundaryMixed := by
    obtain ⟨C, D, hne, hset⟩ := Nat.card_eq_two_iff.mp R.G.boundarySignature.1
    have hCD (E : boundaryComponents R.G) : E = C ∨ E = D := by
      have := hset.symm ▸ Set.mem_univ E
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    intro E
    have hrole := R.boundary_ne
    rcases hCD E with hE | hE <;>
      rcases hCD R.boundaryPure with hp | hp <;>
      rcases hCD R.boundaryMixed with hm | hm <;> grind
  have ho := (boundary_orientation_exhaustion R.G R.boundaryPure R.boundaryMixed
    R.boundary_ne hall R.G.boundarySignature.2).1
  have hp := killed_iff_singleton_predecessor P.M _ R.boundaryPure (R.e 2) R.pureC
  have hm := killed_iff_pair_predecessor P.M _ R.boundaryMixed (R.e 0) (R.e 1) R.mixedAB
  rcases ho with ⟨hpk, hml⟩ | ⟨hpl, hmk⟩
  · exact Or.inl ⟨hp.mp hpk, fun h => hml (hm.mpr (Or.inl h)),
      fun h => hml (hm.mpr (Or.inr h))⟩
  · exact Or.inr ⟨fun h => hpl (hp.mpr h), hm.mp hmk⟩

/-- The primitive normalized lattice retains the pivot: gcd(d,m)=1 is proved. -/
theorem actual_normalization_pivot (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingM B e / Nat.gcd (routingD B e) (routingM B e) = routingM B e := by
  rw [(routingD_coprime_routingM B e).gcd_eq_one, Nat.div_one]

/-- Literal physical K membership, including its scaling, not a name-level cast. -/
theorem actual_scaled_cut_iff (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (x : ℕ) :
    x ∈ cyclicCut (routingH B e) (routingM B e) ↔ routingD B e * x ∈ B.K := by
  rw [actual_cyclicCut_iff_routingI]
  change (∃ y : ℕ, routingD B e * y ∈
    aperyTail Gamma.toAddSubmonoid
      (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e)) B.q.val ∧
      (x : ℤ) = y) ↔ _
  rw [← chosenBase_tail_eq_generatedThree B e]
  change (∃ y : ℕ, routingD B e * y ∈ B.K ∧ (x : ℤ) = y) ↔ _
  constructor
  · rintro ⟨y, hy, heq⟩
    have : x = y := by exact_mod_cast heq
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

abbrev ModelSources (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) := ActualHSources B e

/-- Maximal complement elements in the H-order, entirely on natural degrees. -/
def ModelTop (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (x : ℕ) : Prop :=
  x ∈ routingH B e ∧ x ∉ cyclicCut (routingH B e) (routingM B e) ∧
    ∀ h : ℕ, h ∈ routingH B e → h ≠ 0 →
      x+h ∈ cyclicCut (routingH B e) (routingM B e)

abbrev ModelTops (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  {x : ℕ // ModelTop B e x}

theorem modelTop_cast_iff (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (x : ℕ) :
    ModelTop B e x ↔ IsIntegralSocle (routingI B e) (x : ℤ) := by
  constructor
  · rintro ⟨hx, hn, hall⟩
    refine ⟨⟨x, hx, rfl⟩, fun h => hn ((actual_cyclicCut_iff_routingI B e x).mpr h), ?_⟩
    intro h hh h0
    simpa only [Nat.cast_add] using (actual_cyclicCut_iff_routingI B e (x+h)).mp (hall h hh h0)
  · rintro ⟨⟨n, hn, heq⟩, hx, hall⟩
    have hnx : n = x := by exact_mod_cast heq.symm
    refine ⟨hnx ▸ hn, fun h => hx ((actual_cyclicCut_iff_routingI B e x).mp h), ?_⟩
    intro h hh h0
    apply (actual_cyclicCut_iff_routingI B e (x+h)).mpr
    simpa only [Nat.cast_add] using hall h hh h0

def modelTopsEquivIntegralSocle (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    ModelTops B e ≃ {x : ℤ // IsIntegralSocle (routingI B e) x} where
  toFun x := ⟨x.val, (modelTop_cast_iff B e x.val).mp x.property⟩
  invFun x := ⟨x.val.toNat, (modelTop_cast_iff B e _).mpr (by
    obtain ⟨n, hn, heq⟩ := x.property.1
    have hnon : 0 ≤ x.val := by rw [heq]; positivity
    simpa only [Int.toNat_of_nonneg hnon] using x.property)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by
    apply Subtype.ext
    obtain ⟨n, hn, heq⟩ := x.property.1
    apply Int.toNat_of_nonneg
    rw [heq]
    positivity

theorem actual_model_source_count {P : P2Data Gamma} (R : ActualRolePacket P) :
    Nat.card (ModelSources P.M.base R.e) = P.sourceCount := actual_H_source_count P R.e

theorem actual_model_top_count {P : P2Data Gamma} (R : ActualRolePacket P) :
    Nat.card (ModelTops P.M.base R.e) = Gamma.asRelativeIdeal.idealType :=
  (Nat.card_congr (modelTopsEquivIntegralSocle P.M.base R.e)).trans
    (L5A2C4OR25.actual_integral_socle_card_eq_type P.M.base R.e)

theorem actual_model_sources_finite {P : P2Data Gamma} (R : ActualRolePacket P) :
    Finite (ModelSources P.M.base R.e) :=
  (Nat.card_pos_iff.mp (show 0 < Nat.card (ModelSources P.M.base R.e) by
    rw [actual_model_source_count R]
    exact chosenBase_sourceCount_pos P.M.base)).2

theorem actual_model_tops_finite (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Finite (ModelTops B e) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  letI := finite_pseudoFrobenius_of_generatedByThree (routingI B e)
    (routingA B e) (routingB B e) (routingC B e)
    (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1
  let f : ModelTops B e → {x : ℤ // (routingI B e).IsPseudoFrobenius x} :=
    fun x => ⟨x.val, isIntegralSocle_isPseudoFrobenius (routingI B e)
      ((modelTop_cast_iff B e x.val).mp x.property)⟩
  apply Finite.of_injective f
  intro x y heq
  apply Subtype.ext
  have h : (x.val : ℤ) = y.val := congrArg (fun t => (t.val : ℤ)) heq
  exact_mod_cast h

theorem normalized_b_critical_min (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {r u v : ℕ} (hr : 0 < r)
    (heq : r*routingB B e = u*routingA B e+v*routingC B e) : c2 B e ≤ r := by
  have ha : routingD B e*routingA B e=weights B (e 0) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale B e 1 0 0
  have hb : routingD B e*routingB B e=weights B (e 1) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale B e 0 1 0
  have hc : routingD B e*routingC B e=weights B (e 2) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale B e 0 0 1
  apply criticalExponent_min B (e 1) r
  refine ⟨hr,Finsupp.single (e 0) u+Finsupp.single (e 2) v,by simp,?_⟩
  have hf : r*weights B (e 1)=u*weights B (e 0)+v*weights B (e 2) := by
    nlinarith only [ha,hb,hc,heq]
  simpa [map_add,weight_single] using hf.symm

/-- All three minima refer to the same actual primitive lattice as the cut. -/
theorem actual_normalized_critical_minima {P : P2Data Gamma} (R : ActualRolePacket P) :
    (∀ r u v : ℕ, 0<r → r*routingA P.M.base R.e =
      u*routingB P.M.base R.e+v*routingC P.M.base R.e → c1 P.M.base R.e ≤ r) ∧
    (∀ r u v : ℕ, 0<r → r*routingB P.M.base R.e =
      u*routingA P.M.base R.e+v*routingC P.M.base R.e → c2 P.M.base R.e ≤ r) ∧
    (∀ r u v : ℕ, 0<r → r*routingC P.M.base R.e =
      u*routingA P.M.base R.e+v*routingB P.M.base R.e → c3 P.M.base R.e ≤ r) :=
  ⟨fun _ _ _ => L5A2C4OR26.normalized_a_critical_min _ _,
    L5A2C4OR6.coherent_second_minimality _ _ R.HD,
    L5A2C4OR6.coherent_third_minimality _ _ R.HD⟩

private theorem normalized_predecessor_iff (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (n t : ℕ) :
    n-t ∈ cyclicCut (routingH B e) (routingM B e) ↔
      routingD B e*n-routingD B e*t ∈ B.K := by
  rw [actual_scaled_cut_iff, Nat.mul_sub_left_distrib]

theorem actual_normalized_internal_live {P : P2Data Gamma} (R : ActualRolePacket P) :
    let h := c2 P.M.base R.e * routingB P.M.base R.e
    let K := cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
    h-routingA P.M.base R.e ∉ K ∧ h-routingB P.M.base R.e ∉ K ∧
      h-routingC P.M.base R.e ∉ K := by
  have ha : routingD P.M.base R.e*routingA P.M.base R.e=weights P.M.base (R.e 0) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base R.e 1 0 0
  have hb : routingD P.M.base R.e*routingB P.M.base R.e=weights P.M.base (R.e 1) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base R.e 0 1 0
  have hc : routingD P.M.base R.e*routingC P.M.base R.e=weights P.M.base (R.e 2) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base R.e 0 0 1
  have hs : routingD P.M.base R.e*(c2 P.M.base R.e*routingB P.M.base R.e) =
      R.G.internalDegree := by rw [Nat.mul_left_comm, hb, (actual_critical_role_degrees R).1]
  dsimp only
  simp only [normalized_predecessor_iff, hs, ha, hb, hc]
  exact actual_internal_predecessors_live R

theorem actual_normalized_inactive_killed {P : P2Data Gamma} (R : ActualRolePacket P) :
    let h := c1 P.M.base R.e * routingA P.M.base R.e
    let K := cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
    h-routingA P.M.base R.e ∈ K ∧
      (h-routingB P.M.base R.e ∈ K ∨ h-routingC P.M.base R.e ∈ K) := by
  have ha : routingD P.M.base R.e*routingA P.M.base R.e=weights P.M.base (R.e 0) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base R.e 1 0 0
  have hb : routingD P.M.base R.e*routingB P.M.base R.e=weights P.M.base (R.e 1) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base R.e 0 1 0
  have hc : routingD P.M.base R.e*routingC P.M.base R.e=weights P.M.base (R.e 2) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base R.e 0 0 1
  dsimp only
  simp only [normalized_predecessor_iff, Nat.mul_left_comm (routingD P.M.base R.e), ha, hb, hc]
  exact actual_inactive_predecessors R

theorem actual_normalized_boundary_dichotomy {P : P2Data Gamma} (R : ActualRolePacket P) :
    let h := c3 P.M.base R.e * routingC P.M.base R.e
    let a := routingA P.M.base R.e
    let b := routingB P.M.base R.e
    let c := routingC P.M.base R.e
    let K := cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
    (h-c ∈ K ∧ h-a ∉ K ∧ h-b ∉ K) ∨ (h-c ∉ K ∧ (h-a ∈ K ∨ h-b ∈ K)) := by
  have ha : routingD P.M.base R.e*routingA P.M.base R.e=weights P.M.base (R.e 0) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base R.e 1 0 0
  have hb : routingD P.M.base R.e*routingB P.M.base R.e=weights P.M.base (R.e 1) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base R.e 0 1 0
  have hc : routingD P.M.base R.e*routingC P.M.base R.e=weights P.M.base (R.e 2) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base R.e 0 0 1
  have hs : routingD P.M.base R.e*(c3 P.M.base R.e*routingC P.M.base R.e) =
      R.G.boundaryDegree := by rw [Nat.mul_left_comm, hc, (actual_critical_role_degrees R).2]
  dsimp only
  simp only [normalized_predecessor_iff, hs, ha, hb, hc]
  exact actual_boundary_predecessor_dichotomy R

end NS25Lean.L5A2C4OR29
