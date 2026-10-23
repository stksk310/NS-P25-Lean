import NS25Lean.P2CriticalSupportReindexing

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR4R1

open ChosenBase L2B L5A1 L5A2B4AR4

variable {Gamma : NumericalSemigroup}

/-- A component supported on exactly two variables contains one actual
factorization using both variables.  The witness is selected from the
component, not from the arbitrary R3 critical-exponent choice. -/
theorem exists_mixed_factorization_of_componentSupport_pair
    (B : Data Gamma) (h : ℕ) (C : FiberComponent B h) (j k : Fin 3)
    (hjk : j ≠ k) (hC : componentSupport B h C = {j, k}) :
    ∃ u : FactorizationFiber B h,
      (fiberGraph B h).connectedComponentMk u = C ∧
        0 < u.val j ∧ 0 < u.val k := by
  classical
  obtain ⟨uj, hujC, hujj⟩ :=
    (mem_componentSupport B h C j).mp (by simp [hC])
  obtain ⟨uk, hukC, hukk⟩ :=
    (mem_componentSupport B h C k).mp (by simp [hC])
  by_contra hnone
  push Not at hnone
  have hedge : ∀ {x y : FactorizationFiber B h},
      (fiberGraph B h).Adj x y →
      (fiberGraph B h).connectedComponentMk x = C →
      0 < x.val j → 0 < y.val j := by
    intro x y hxy hxC hxj
    obtain ⟨_, q, hxq, hyq⟩ := hxy
    by_cases hqj : q = j
    · simpa [hqj] using hyq
    have hqmem : q ∈ componentSupport B h C :=
      (mem_componentSupport B h C q).mpr ⟨x, hxC, hxq⟩
    have hqk : q = k := by
      rw [hC] at hqmem
      simpa [hqj] using hqmem
    subst q
    exact (Nat.not_lt_of_ge (hnone x hxC hxj) hxq).elim
  have hprop : ∀ {x y : FactorizationFiber B h},
      (fiberGraph B h).Reachable x y →
      (fiberGraph B h).connectedComponentMk x = C →
      0 < x.val j → 0 < y.val j := by
    intro x y hxy hxC hxj
    obtain ⟨p⟩ := hxy
    induction p with
    | nil => exact hxj
    | @cons x y z hxy p ih =>
        have hyj := hedge hxy hxC hxj
        have hyC : (fiberGraph B h).connectedComponentMk y = C :=
          (SimpleGraph.ConnectedComponent.sound hxy.reachable).symm.trans hxC
        exact ih hyC hyj
  have hreach := SimpleGraph.ConnectedComponent.exact (hujC.trans hukC.symm)
  have hukj := hprop hreach hujC hujj
  exact (Nat.not_lt_of_ge (hnone uk hukC hukj) hukk).elim

/-- Every coordinate outside a component support is zero on every actual
vertex of that component. -/
theorem coordinate_eq_zero_of_not_mem_componentSupport
    (B : Data Gamma) (h : ℕ) (C : FiberComponent B h)
    (u : FactorizationFiber B h)
    (huC : (fiberGraph B h).connectedComponentMk u = C) (j : Fin 3)
    (hj : j ∉ componentSupport B h C) : u.val j = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro huj
  exact hj ((mem_componentSupport B h C j).mpr ⟨u, huC, huj⟩)

/-- Source-exact extraction of the unique variable of a singleton support. -/
theorem exists_variable_of_componentSupport_card_eq_one
    (B : Data Gamma) (h : ℕ) (C : FiberComponent B h)
    (hC : (componentSupport B h C).card = 1) :
    ∃ j : Fin 3, componentSupport B h C = {j} :=
  Finset.card_eq_one.mp hC

/-- The complete actual critical role carried by a pure/mixed positive
two-component fiber. -/
structure PureMixedCriticalRole (B : Data Gamma) (h : ℕ) where
  degree_pos : 0 < h
  componentCount_eq_two : componentCount B h = 2
  pureComponent : FiberComponent B h
  mixedComponent : FiberComponent B h
  components_ne : pureComponent ≠ mixedComponent
  pureRole : Fin 3
  otherLeft : Fin 3
  otherRight : Fin 3
  other_ne : otherLeft ≠ otherRight
  pure_ne_left : pureRole ≠ otherLeft
  pure_ne_right : pureRole ≠ otherRight
  roles_cover : ({pureRole, otherLeft, otherRight} : Finset (Fin 3)) = Finset.univ
  pureSupport : componentSupport B h pureComponent = {pureRole}
  mixedSupport : componentSupport B h mixedComponent = {otherLeft, otherRight}
  degree_eq_critical : h = criticalExponent B pureRole * weights B pureRole
  witness : FactorizationFiber B h
  witness_component : (fiberGraph B h).connectedComponentMk witness = mixedComponent
  witness_pure_zero : witness.val pureRole = 0
  witness_left_pos : 0 < witness.val otherLeft
  witness_right_pos : 0 < witness.val otherRight

/-- Construct a pure/mixed critical role solely from actual component
supports and the generic mixed-vertex theorem. -/
theorem pureMixedCriticalRole_of_components
    (B : Data Gamma) (h : ℕ) (hpos : 0 < h)
    (hcount : componentCount B h = 2)
    (pure mixed : FiberComponent B h) (hne : pure ≠ mixed)
    (hpure : (componentSupport B h pure).card = 1)
    (hmixed : (componentSupport B h mixed).card = 2) :
    Nonempty (PureMixedCriticalRole B h) := by
  classical
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hpure
  obtain ⟨k, l, hkl, hklSupport⟩ := Finset.card_eq_two.mp hmixed
  have hdis := componentSupports_disjoint B h pure mixed hne
  have hsetdis : Disjoint ({j} : Finset (Fin 3)) ({k, l} : Finset (Fin 3)) := by
    simpa [hj, hklSupport] using hdis
  have hjk : j ≠ k := by
    intro he
    subst k
    exact Finset.disjoint_left.mp hsetdis
      (show j ∈ ({j} : Finset (Fin 3)) by simp)
      (show j ∈ ({j, l} : Finset (Fin 3)) by simp)
  have hjl : j ≠ l := by
    intro he
    subst l
    exact Finset.disjoint_left.mp hsetdis
      (show j ∈ ({j} : Finset (Fin 3)) by simp)
      (show j ∈ ({k, j} : Finset (Fin 3)) by simp)
  have hcover : ({j, k, l} : Finset (Fin 3)) = Finset.univ := by
    have hcard : (({j} : Finset (Fin 3)) ∪ {k, l}).card = 3 := by
      rw [Finset.card_union_of_disjoint hsetdis]
      simp [hkl]
    have hunion : ({j} : Finset (Fin 3)) ∪ {k, l} = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using hcard)
    calc
      ({j, k, l} : Finset (Fin 3)) = ({j} : Finset (Fin 3)) ∪ {k, l} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      _ = Finset.univ := hunion
  obtain ⟨u, huC, huk, hul⟩ :=
    exists_mixed_factorization_of_componentSupport_pair B h mixed k l hkl hklSupport
  have huj : u.val j = 0 :=
    coordinate_eq_zero_of_not_mem_componentSupport B h mixed u huC j (by
      rw [hklSupport]
      simp [hjk, hjl])
  have hactive : 1 < componentCount B h := by omega
  have hcritical := singleton_active_degree_eq_critical B h hpos hactive pure j hj
  exact ⟨{
    degree_pos := hpos
    componentCount_eq_two := hcount
    pureComponent := pure
    mixedComponent := mixed
    components_ne := hne
    pureRole := j
    otherLeft := k
    otherRight := l
    other_ne := hkl
    pure_ne_left := hjk
    pure_ne_right := hjl
    roles_cover := hcover
    pureSupport := hj
    mixedSupport := hklSupport
    degree_eq_critical := hcritical
    witness := u
    witness_component := huC
    witness_pure_zero := huj
    witness_left_pos := huk
    witness_right_pos := hul
  }⟩

theorem PureMixedCriticalRole.witness_pos_of_mem_mixedSupport
    {B : Data Gamma} {h : ℕ} (R : PureMixedCriticalRole B h) (i : Fin 3)
    (hi : i ∈ componentSupport B h R.mixedComponent) : 0 < R.witness.val i := by
  rw [R.mixedSupport] at hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact R.witness_left_pos
  · exact R.witness_right_pos

/-- The two source-exact critical roles carried by a pure/pure positive
two-component fiber. -/
structure PurePureCriticalPair (B : Data Gamma) (h : ℕ) where
  degree_pos : 0 < h
  componentCount_eq_two : componentCount B h = 2
  leftComponent : FiberComponent B h
  rightComponent : FiberComponent B h
  components_ne : leftComponent ≠ rightComponent
  leftRole : Fin 3
  rightRole : Fin 3
  roles_ne : leftRole ≠ rightRole
  leftSupport : componentSupport B h leftComponent = {leftRole}
  rightSupport : componentSupport B h rightComponent = {rightRole}
  left_degree_eq_critical : h = criticalExponent B leftRole * weights B leftRole
  right_degree_eq_critical : h = criticalExponent B rightRole * weights B rightRole
  leftWitness : FactorizationFiber B h
  rightWitness : FactorizationFiber B h
  leftWitness_component :
    (fiberGraph B h).connectedComponentMk leftWitness = leftComponent
  rightWitness_component :
    (fiberGraph B h).connectedComponentMk rightWitness = rightComponent
  leftWitness_pure :
    leftWitness.val = Finsupp.single leftRole (leftWitness.val leftRole)
  rightWitness_pure :
    rightWitness.val = Finsupp.single rightRole (rightWitness.val rightRole)

/-- Construct the two critical singleton roles and actual pure vertices from
a pure/pure fiber. -/
theorem purePureCriticalPair_of_components
    (B : Data Gamma) (h : ℕ) (hpos : 0 < h)
    (hcount : componentCount B h = 2)
    (left right : FiberComponent B h) (hne : left ≠ right)
    (hleft : (componentSupport B h left).card = 1)
    (hright : (componentSupport B h right).card = 1) :
    Nonempty (PurePureCriticalPair B h) := by
  classical
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hleft
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hright
  have hjk : j ≠ k := by
    intro he
    subst k
    exact hne (components_eq_of_shared_support B h left right j (by simp [hj]) (by simp [hk]))
  obtain ⟨u, hu⟩ := left.exists_rep
  obtain ⟨v, hv⟩ := right.exists_rep
  have hactive : 1 < componentCount B h := by omega
  exact ⟨{
    degree_pos := hpos
    componentCount_eq_two := hcount
    leftComponent := left
    rightComponent := right
    components_ne := hne
    leftRole := j
    rightRole := k
    roles_ne := hjk
    leftSupport := hj
    rightSupport := hk
    left_degree_eq_critical :=
      singleton_active_degree_eq_critical B h hpos hactive left j hj
    right_degree_eq_critical :=
      singleton_active_degree_eq_critical B h hpos hactive right k hk
    leftWitness := u
    rightWitness := v
    leftWitness_component := hu
    rightWitness_component := hv
    leftWitness_pure := fiber_eq_single_of_componentSupport B h left j hj u hu
    rightWitness_pure := fiber_eq_single_of_componentSupport B h right k hk v hv
  }⟩

/-- Pure singleton roles at distinct positive active degrees are distinct. -/
theorem pure_roles_ne_of_degree_ne
    (B : Data Gamma) (h g : ℕ) (hne : h ≠ g)
    (hhpos : 0 < h) (hgpos : 0 < g)
    (hhcount : componentCount B h = 2) (hgcount : componentCount B g = 2)
    (C : FiberComponent B h) (E : FiberComponent B g)
    (j k : Fin 3) (hC : componentSupport B h C = {j})
    (hE : componentSupport B g E = {k}) : j ≠ k := by
  intro hjk
  subst k
  exact hne (singleton_active_degree_unique B h g hhpos hgpos
    (by omega) (by omega) C E j hC hE)

private theorem exists_third_fin3 (j k : Fin 3) (hjk : j ≠ k) :
    ∃ l : Fin 3, l ≠ j ∧ l ≠ k := by
  fin_cases j <;> fin_cases k
  · exact (hjk rfl).elim
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact (hjk rfl).elim
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact (hjk rfl).elim

private def fin3EquivOfDistinct (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ≃ Fin 3 :=
  Equiv.ofBijective (![a, b, c] : Fin 3 → Fin 3)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc], rfl⟩)

@[simp] private theorem fin3EquivOfDistinct_zero (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    fin3EquivOfDistinct a b c hab hac hbc 0 = a := rfl

@[simp] private theorem fin3EquivOfDistinct_one (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    fin3EquivOfDistinct a b c hab hac hbc 1 = b := rfl

@[simp] private theorem fin3EquivOfDistinct_two (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    fin3EquivOfDistinct a b c hab hac hbc 2 = c := rfl

private theorem support_pair_eq_other_two (B : Data Gamma) (h : ℕ)
    (C : FiberComponent B h) (e : Fin 3 ≃ Fin 3)
    (hcard : (componentSupport B h C).card = 2)
    (hzero : e 0 ∉ componentSupport B h C) :
    componentSupport B h C = {e 1, e 2} := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨i, rfl⟩ := e.surjective j
    fin_cases i
    · exact (hzero hj).elim
    · simp
    · simp
  · simpa [hcard, e.injective.eq_iff]

private theorem purePureCriticalPair_of_all_singleton
    (B : Data Gamma) (h : ℕ) (hpos : 0 < h)
    (hcount : componentCount B h = 2)
    (hall : ∀ C : FiberComponent B h,
      (componentSupport B h C).card = 1) :
    Nonempty (PurePureCriticalPair B h) := by
  classical
  obtain ⟨C, D, hne, _⟩ := Nat.card_eq_two_iff.mp hcount
  exact purePureCriticalPair_of_components B h hpos hcount C D hne (hall C) (hall D)

private theorem pureMixedCriticalRole_of_shape
    (B : Data Gamma) (h : ℕ) (hpos : 0 < h)
    (hcount : componentCount B h = 2)
    (hshape : ∃ C D : FiberComponent B h, C ≠ D ∧
      (((componentSupport B h C).card = 1 ∧
          (componentSupport B h D).card = 2) ∨
        ((componentSupport B h C).card = 2 ∧
          (componentSupport B h D).card = 1)) ∧
      ∀ E : FiberComponent B h, E = C ∨ E = D) :
    Nonempty (PureMixedCriticalRole B h) := by
  obtain ⟨C, D, hne, hCD, _⟩ := hshape
  rcases hCD with hCD | hDC
  · exact pureMixedCriticalRole_of_components B h hpos hcount C D hne hCD.1 hCD.2
  · exact pureMixedCriticalRole_of_components B h hpos hcount D C hne.symm hDC.2 hDC.1

/-- Branch A contains the two pure roles at one actual degree and the
source-exact mixed critical role at the other; the derived permutation proves
that these three pure roles exhaust `Fin 3`. -/
structure SectorBCriticalRoleBranchA (P : P2Data Gamma) where
  pairDegree : ℕ
  mixedDegree : ℕ
  degree_ne : pairDegree ≠ mixedDegree
  positiveDegrees_eq : positiveDegrees P.M = {pairDegree, mixedDegree}
  pair : PurePureCriticalPair P.M.base pairDegree
  mixed : PureMixedCriticalRole P.M.base mixedDegree
  mixed_ne_left : mixed.pureRole ≠ pair.leftRole
  mixed_ne_right : mixed.pureRole ≠ pair.rightRole
  reindex : Fin 3 ≃ Fin 3
  reindex_zero : reindex 0 = pair.leftRole
  reindex_one : reindex 1 = pair.rightRole
  reindex_two : reindex 2 = mixed.pureRole

/-- Branch B contains exactly the two actual mixed critical roles and the
remaining third variable.  No critical witness for that remaining role is
part of this package. -/
structure SectorBCriticalRoleBranchB (P : P2Data Gamma) where
  firstDegree : ℕ
  secondDegree : ℕ
  degree_ne : firstDegree ≠ secondDegree
  positiveDegrees_eq : positiveDegrees P.M = {firstDegree, secondDegree}
  first : PureMixedCriticalRole P.M.base firstDegree
  second : PureMixedCriticalRole P.M.base secondDegree
  pure_roles_ne : first.pureRole ≠ second.pureRole
  remainingRole : Fin 3
  remaining_ne_first : remainingRole ≠ first.pureRole
  remaining_ne_second : remainingRole ≠ second.pureRole
  reindex : Fin 3 ≃ Fin 3
  reindex_zero : reindex 0 = first.pureRole
  reindex_one : reindex 1 = second.pureRole
  reindex_two : reindex 2 = remainingRole
  first_mixed_support :
    componentSupport P.M.base firstDegree first.mixedComponent = {reindex 1, reindex 2}
  second_mixed_support :
    componentSupport P.M.base secondDegree second.mixedComponent = {reindex 0, reindex 2}
  first_witness_one_pos : 0 < first.witness.val (reindex 1)
  first_witness_two_pos : 0 < first.witness.val (reindex 2)
  second_witness_zero_pos : 0 < second.witness.val (reindex 0)
  second_witness_two_pos : 0 < second.witness.val (reindex 2)

private theorem branchA_of_pair_mixed (P : P2Data Gamma)
    {h g : ℕ} (hne : h ≠ g) (hdegrees : positiveDegrees P.M = {h, g})
    (A : PurePureCriticalPair P.M.base h)
    (R : PureMixedCriticalRole P.M.base g) :
    Nonempty (SectorBCriticalRoleBranchA P) := by
  have hRL : R.pureRole ≠ A.leftRole :=
    pure_roles_ne_of_degree_ne P.M.base g h hne.symm
      R.degree_pos A.degree_pos R.componentCount_eq_two A.componentCount_eq_two
      R.pureComponent A.leftComponent R.pureRole A.leftRole R.pureSupport A.leftSupport
  have hRR : R.pureRole ≠ A.rightRole :=
    pure_roles_ne_of_degree_ne P.M.base g h hne.symm
      R.degree_pos A.degree_pos R.componentCount_eq_two A.componentCount_eq_two
      R.pureComponent A.rightComponent R.pureRole A.rightRole R.pureSupport A.rightSupport
  let e := fin3EquivOfDistinct A.leftRole A.rightRole R.pureRole
    A.roles_ne (Ne.symm hRL) (Ne.symm hRR)
  exact ⟨{
    pairDegree := h
    mixedDegree := g
    degree_ne := hne
    positiveDegrees_eq := hdegrees
    pair := A
    mixed := R
    mixed_ne_left := hRL
    mixed_ne_right := hRR
    reindex := e
    reindex_zero := by simp [e]
    reindex_one := by simp [e]
    reindex_two := by simp [e]
  }⟩

private theorem branchB_of_mixed_mixed (P : P2Data Gamma)
    {h g : ℕ} (hne : h ≠ g) (hdegrees : positiveDegrees P.M = {h, g})
    (R : PureMixedCriticalRole P.M.base h)
    (S : PureMixedCriticalRole P.M.base g) :
    Nonempty (SectorBCriticalRoleBranchB P) := by
  classical
  have hrs : R.pureRole ≠ S.pureRole :=
    pure_roles_ne_of_degree_ne P.M.base h g hne
      R.degree_pos S.degree_pos R.componentCount_eq_two S.componentCount_eq_two
      R.pureComponent S.pureComponent R.pureRole S.pureRole R.pureSupport S.pureSupport
  obtain ⟨l, hlj, hlk⟩ := exists_third_fin3 R.pureRole S.pureRole hrs
  let e := fin3EquivOfDistinct R.pureRole S.pureRole l hrs (Ne.symm hlj) (Ne.symm hlk)
  have hRzero : e 0 ∉ componentSupport P.M.base h R.mixedComponent := by
    rw [show e 0 = R.pureRole by simp [e], R.mixedSupport]
    simp [R.pure_ne_left, R.pure_ne_right]
  have hSzero : e 1 ∉ componentSupport P.M.base g S.mixedComponent := by
    rw [show e 1 = S.pureRole by simp [e], S.mixedSupport]
    simp [S.pure_ne_left, S.pure_ne_right]
  have hRsupport := support_pair_eq_other_two P.M.base h R.mixedComponent e
    (by rw [R.mixedSupport]; simp [R.other_ne]) hRzero
  have hSsupport : componentSupport P.M.base g S.mixedComponent = {e 0, e 2} := by
    have he := support_pair_eq_other_two P.M.base g S.mixedComponent
      ((Equiv.swap 0 1).trans e)
      (by rw [S.mixedSupport]; simp [S.other_ne]) (by
        change e 1 ∉ componentSupport P.M.base g S.mixedComponent
        exact hSzero)
    have hswap1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
    have hswap2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    simp only [Equiv.trans_apply] at he
    rw [hswap1, hswap2] at he
    simpa [Finset.pair_comm] using he
  exact ⟨{
    firstDegree := h
    secondDegree := g
    degree_ne := hne
    positiveDegrees_eq := hdegrees
    first := R
    second := S
    pure_roles_ne := hrs
    remainingRole := l
    remaining_ne_first := hlj
    remaining_ne_second := hlk
    reindex := e
    reindex_zero := by simp [e]
    reindex_one := by simp [e]
    reindex_two := by simp [e]
    first_mixed_support := hRsupport
    second_mixed_support := hSsupport
    first_witness_one_pos := R.witness_pos_of_mem_mixedSupport (e 1) (by
      rw [hRsupport]
      simp)
    first_witness_two_pos := R.witness_pos_of_mem_mixedSupport (e 2) (by
      rw [hRsupport]
      simp)
    second_witness_zero_pos := S.witness_pos_of_mem_mixedSupport (e 0) (by
      rw [hSsupport]
      simp)
    second_witness_two_pos := S.witness_pos_of_mem_mixedSupport (e 2) (by
      rw [hSsupport]
      simp)
  }⟩

/-- The exact source-derived critical-role dichotomy for the two actual
Sector-B fibers. -/
theorem sectorB_criticalRole_dichotomy
    (P : P2Data Gamma) (hB : SectorB P.M) :
    Nonempty (SectorBCriticalRoleBranchA P) ∨
      Nonempty (SectorBCriticalRoleBranchB P) := by
  obtain ⟨h, g, hne, hdegrees, hhcount, hgcount, hhpos, hgpos,
    hhshape, hgshape, hnotboth⟩ := sectorB_actual_support_shape_checkpoint P hB
  rcases hhshape with hhpure | hhmixed
  · rcases hgshape with hgpure | hgmixed
    · exact (hnotboth ⟨hhpure, hgpure⟩).elim
    · obtain ⟨A⟩ := purePureCriticalPair_of_all_singleton P.M.base h hhpos hhcount hhpure
      obtain ⟨R⟩ := pureMixedCriticalRole_of_shape P.M.base g hgpos hgcount hgmixed
      exact Or.inl (branchA_of_pair_mixed P hne hdegrees A R)
  · rcases hgshape with hgpure | hgmixed
    · obtain ⟨A⟩ := purePureCriticalPair_of_all_singleton P.M.base g hgpos hgcount hgpure
      obtain ⟨R⟩ := pureMixedCriticalRole_of_shape P.M.base h hhpos hhcount hhmixed
      have hdegrees' : positiveDegrees P.M = {g, h} := by
        simpa [Finset.pair_comm] using hdegrees
      exact Or.inl (branchA_of_pair_mixed P hne.symm hdegrees' A R)
    · obtain ⟨R⟩ := pureMixedCriticalRole_of_shape P.M.base h hhpos hhcount hhmixed
      obtain ⟨S⟩ := pureMixedCriticalRole_of_shape P.M.base g hgpos hgcount hgmixed
      exact Or.inr (branchB_of_mixed_mixed P hne hdegrees R S)

end NS25Lean.L5A2B4AR4R1
