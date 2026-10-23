import NS25Lean.P2Sectors
import NS25Lean.FourBasePreparation
import NS25Lean.OneDefectBetti

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A1

open ChosenBase

variable {Gamma : NumericalSemigroup}

/-- An actual pure tail factorization on the displayed tail role `j`. -/
def TailPureAt (B : Data Gamma) (L : ℕ) (j : Fin 3) : Prop :=
  ∃ u : L2B.FactorizationFiber B L,
    u.val = Finsupp.single j (u.val j) ∧ 0 < u.val j

/-- An actual pure full factorization on the displayed four-generator role `i`. -/
def FullPureAt (B : Data Gamma) (L : ℕ) (i : Fin 4) : Prop :=
  ∃ u : L2C.FactorizationFiber B L,
    u.val = Finsupp.single i (u.val i) ∧ 0 < u.val i

theorem tail_fiber_eq_single_of_componentSupport (B : Data Gamma) (L : ℕ)
    (C : L2B.FiberComponent B L) (j : Fin 3)
    (hs : L2B.componentSupport B L C = {j})
    (u : L2B.FactorizationFiber B L)
    (hu : (L2B.fiberGraph B L).connectedComponentMk u = C) :
    u.val = Finsupp.single j (u.val j) := by
  ext i
  by_cases he : i = j
  · subst i
    simp
  · rw [Finsupp.single_eq_of_ne he]
    by_contra hn
    have hi := (L2B.mem_componentSupport B L C i).mpr
      ⟨u, hu, Nat.pos_of_ne_zero hn⟩
    rw [hs, Finset.mem_singleton] at hi
    exact he hi

/-- The three tail components in Sector Y are pure and exhaust the three tail roles. -/
theorem sectorY_tail_three_pure_powers (P : P2Data Gamma) (hY : SectorY P.M) :
    ∃ L : ℕ, 0 < L ∧
      L2B.componentCount P.M.base L = 3 ∧
      L2B.killedCount P.M L = 0 ∧
      ∀ j : Fin 3, TailPureAt P.M.base L j := by
  classical
  rcases hY with ⟨L, hdegrees, hcomponents, hkilled⟩
  have hLpos : 0 < L := by
    have hmem : L ∈ positiveDegrees P.M := by simp [hdegrees]
    exact (positive_contribution_active P.M L
      ((mem_positiveDegrees P.M L).mp hmem)).1
  let role : L2B.FiberComponent P.M.base L → Fin 3 := fun C =>
    Classical.choose (Finset.card_eq_one.mp
      (componentSupport_card_eq_one_of_three P.M L hLpos hcomponents C))
  have hrole (C : L2B.FiberComponent P.M.base L) :
      L2B.componentSupport P.M.base L C = {role C} :=
    Classical.choose_spec (Finset.card_eq_one.mp
      (componentSupport_card_eq_one_of_three P.M L hLpos hcomponents C))
  have hinj : Function.Injective role := by
    intro C E he
    apply L2B.components_eq_of_shared_support P.M.base L C E (role C)
    · simp [hrole C]
    · rw [he]
      simp [hrole E]
  have hcard : Nat.card (L2B.FiberComponent P.M.base L) = Nat.card (Fin 3) := by
    simpa [L2B.componentCount] using hcomponents
  have hsurj : Function.Surjective role :=
    ((Nat.bijective_iff_injective_and_card role).mpr ⟨hinj, hcard⟩).2
  refine ⟨L, hLpos, hcomponents, hkilled, ?_⟩
  intro j
  obtain ⟨C, hC⟩ := hsurj j
  obtain ⟨u, hu⟩ := C.exists_rep
  have hpure := tail_fiber_eq_single_of_componentSupport P.M.base L C j
    ((hrole C).trans (congrArg (fun i : Fin 3 => ({i} : Finset (Fin 3))) hC)) u hu
  have hpos : 0 < u.val j := by
    by_contra hn
    have hz : u.val = 0 := by
      rw [hpure]
      simp only [Nat.not_lt, Nat.le_zero] at hn
      simp [hn]
    have := u.property
    rw [hz, map_zero] at this
    omega
  exact ⟨u, hpure, hpos⟩

/-- Full factorizations with zero original-pivot coordinate are exactly lifted tail
factorizations.  No Apéry hypothesis is used. -/
def tailFiberEquivPivotZero (B : Data Gamma) (L : ℕ) :
    L2B.FactorizationFiber B L ≃
      {v : L2C.FactorizationFiber B L // v.val B.pivot = 0} := by
  let f : L2B.FactorizationFiber B L →
      {v : L2C.FactorizationFiber B L // v.val B.pivot = 0} := fun u =>
    ⟨⟨L2C.tailLift B u.val, (L2C.weight_tailLift B u.val).trans u.property⟩,
      L2C.tailLift_pivot_zero B u.val⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v he
    exact Subtype.ext (L2C.tailLift_injective B
      (congrArg (fun x => x.val.val) he))
  · rintro ⟨v, hv⟩
    have hrange : v.val ∈
        Set.range (Finsupp.mapDomain (fun j : Fin 3 => B.order j.succ)) := by
      apply (Finsupp.mem_range_mapDomain_iff _
        (B.order.injective.comp (Fin.succ_injective 3)) _).mpr
      intro i hi
      have he : i = B.pivot := by
        by_contra hn
        exact hi (L3B.exists_tail_index B i hn)
      simpa [he] using hv
    obtain ⟨u, hu⟩ := hrange
    have hu' : L2C.tailLift B u = v.val := hu
    let u' : L2B.FactorizationFiber B L := ⟨u, by
      rw [← L2C.weight_tailLift, hu']
      exact v.property⟩
    refine ⟨u', ?_⟩
    apply Subtype.ext
    exact Subtype.ext hu'

@[simp] theorem tailFiberEquivPivotZero_val (B : Data Gamma) (L : ℕ)
    (u : L2B.FactorizationFiber B L) :
    (tailFiberEquivPivotZero B L u).val.val = L2C.tailLift B u.val := rfl

theorem no_boundaryKilled_of_killedCount_zero (M : L2B.MultiplicityBase Gamma)
    (L : ℕ) (hk : L2B.killedCount M L = 0)
    (C : L2B.FiberComponent M.base L) : ¬L2B.BoundaryKilled M L C := by
  intro hC
  have hpos : 0 < Nat.card
      {E : L2B.FiberComponent M.base L // L2B.BoundaryKilled M L E} :=
    Nat.card_pos_iff.mpr ⟨⟨C, hC⟩, inferInstance⟩
  change Nat.card
    {E : L2B.FiberComponent M.base L // L2B.BoundaryKilled M L E} = 0 at hk
  omega

/-- Source-exact mixed-factor exclusion: the pure tail predecessor is in `H`,
the mixed full factorization puts its pivot predecessor in `Gamma`, hence the
tail component is boundary-killed. -/
theorem mixed_full_factorization_boundaryKilled
    (M : L2B.MultiplicityBase Gamma) (L : ℕ) (j : Fin 3)
    (u : L2B.FactorizationFiber M.base L)
    (hupure : u.val = Finsupp.single j (u.val j)) (huj : 0 < u.val j)
    (v : L2C.FactorizationFiber M.base L)
    (hvp : 0 < v.val M.base.pivot)
    (hvj : 0 < v.val (M.base.order j.succ)) :
    L2B.BoundaryKilled M L
      ((L2B.fiberGraph M.base L).connectedComponentMk u) := by
  have htailWeight : L2C.weights M.base (M.base.order j.succ) =
      L2B.weights M.base j := rfl
  have hpivotWeight : L2C.weights M.base M.base.pivot = M.base.q.val := rfl
  have hdegree : L = u.val j * L2B.weights M.base j := by
    calc
      L = L2B.weight M.base u.val := u.property.symm
      _ = L2B.weight M.base (Finsupp.single j (u.val j)) := congrArg _ hupure
      _ = u.val j * L2B.weights M.base j := L2B.weight_single M.base j _
  have hH : L - L2B.weights M.base j ∈ M.base.H := by
    let a : ℕ := u.val j
    let n : ℕ := L2B.weights M.base j
    have hdegree' : L = a * n := by simpa [a, n] using hdegree
    have he : L - L2B.weights M.base j =
        (u.val j - 1) * L2B.weights M.base j := by
      have he' : L - n = (a - 1) * n := calc
        L - n = a * n - n := congrArg (fun x => x - n) hdegree'
        _ = a * n - 1 * n := by simp
        _ = (a - 1) * n := (Nat.sub_mul a 1 n).symm
      simpa [a, n] using he'
    rw [he]
    exact M.base.H.nsmul_mem (M.base.tailDegrees j).property _
  have hne : M.base.order j.succ ≠ M.base.pivot := by
    intro he
    have hzero : M.base.order 0 = M.base.pivot := by simp [Data.order]
    exact Fin.succ_ne_zero j (M.base.order.injective (he.trans hzero.symm))
  have hremoveTail := L2C.remove_copies M.base v.val (M.base.order j.succ) 1 hvj
  rw [one_mul, v.property, htailWeight] at hremoveTail
  have hpivotAfter : 0 <
      (v.val - Finsupp.single (M.base.order j.succ) 1 : Fin 4 →₀ ℕ)
        M.base.pivot := by
    change 0 < v.val M.base.pivot -
      Finsupp.single (M.base.order j.succ) 1 M.base.pivot
    rw [Finsupp.single_eq_of_ne (Ne.symm hne)]
    simpa using hvp
  have hremovePivot := L2C.remove_copies M.base
    (v.val - Finsupp.single (M.base.order j.succ) 1) M.base.pivot 1 hpivotAfter
  rw [one_mul, hpivotWeight] at hremovePivot
  have hGamma : (L - L2B.weights M.base j) - M.base.q.val ∈ Gamma := by
    have he : (L - L2B.weights M.base j) - M.base.q.val =
        L2C.weight M.base
          ((v.val - Finsupp.single (M.base.order j.succ) 1) -
            Finsupp.single M.base.pivot 1) := by omega
    rw [he]
    exact L2C.weight_mem M.base _
  have hK : L - L2B.weights M.base j ∈ M.base.K := by
    exact ⟨hH, by omega, hGamma⟩
  exact ⟨u, rfl, j, huj, hK⟩

theorem pivot_factorization_is_pure_of_killedCount_zero
    (M : L2B.MultiplicityBase Gamma) (L : ℕ)
    (hk : L2B.killedCount M L = 0)
    (htail : ∀ j : Fin 3, TailPureAt M.base L j)
    (v : L2C.FactorizationFiber M.base L)
    (hvp : 0 < v.val M.base.pivot) :
    v.val = Finsupp.single M.base.pivot (v.val M.base.pivot) := by
  ext i
  by_cases hip : i = M.base.pivot
  · subst i
    simp
  · rw [Finsupp.single_eq_of_ne hip]
    by_contra hi
    obtain ⟨j, rfl⟩ := L3B.exists_tail_index M.base i hip
    obtain ⟨u, hupure, huj⟩ := htail j
    exact no_boundaryKilled_of_killedCount_zero M L hk _
      (mixed_full_factorization_boundaryKilled M L j u hupure huj v hvp
        (Nat.pos_of_ne_zero hi))

theorem tail_factorization_is_pure_of_three_components
    (M : L2B.MultiplicityBase Gamma) (L : ℕ) (hL : 0 < L)
    (hc : L2B.componentCount M.base L = 3)
    (u : L2B.FactorizationFiber M.base L) :
    ∃ j : Fin 3, u.val = Finsupp.single j (u.val j) ∧ 0 < u.val j := by
  let C := (L2B.fiberGraph M.base L).connectedComponentMk u
  have hcard := componentSupport_card_eq_one_of_three M L hL hc C
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hpure := tail_fiber_eq_single_of_componentSupport M.base L C j hj u rfl
  refine ⟨j, hpure, ?_⟩
  by_contra hn
  have hz : u.val = 0 := by
    rw [hpure]
    have : u.val j = 0 := by omega
    simp [this]
  have := u.property
  rw [hz, map_zero] at this
  omega

theorem tailLift_single (B : Data Gamma) (j : Fin 3) (r : ℕ) :
    L2C.tailLift B (Finsupp.single j r) =
      Finsupp.single (B.order j.succ) r := by
  exact Finsupp.mapDomain_single

theorem tailPureAt_fullPureAt (B : Data Gamma) (L : ℕ) (j : Fin 3)
    (h : TailPureAt B L j) : FullPureAt B L (B.order j.succ) := by
  obtain ⟨u, hupure, huj⟩ := h
  let v : L2C.FactorizationFiber B L :=
    ⟨L2C.tailLift B u.val, (L2C.weight_tailLift B u.val).trans u.property⟩
  refine ⟨v, ?_, ?_⟩
  · change L2C.tailLift B u.val =
      Finsupp.single (B.order j.succ) (L2C.tailLift B u.val (B.order j.succ))
    calc
      L2C.tailLift B u.val = L2C.tailLift B (Finsupp.single j (u.val j)) :=
        congrArg _ hupure
      _ = Finsupp.single (B.order j.succ) (u.val j) := tailLift_single B j _
      _ = _ := by rw [L3B.tailLift_at_tail]
  · simpa [v, L3B.tailLift_at_tail] using huj

theorem full_factorization_is_pure_of_sectorY_data
    (M : L2B.MultiplicityBase Gamma) (L : ℕ) (hL : 0 < L)
    (hc : L2B.componentCount M.base L = 3)
    (hk : L2B.killedCount M L = 0)
    (htail : ∀ j : Fin 3, TailPureAt M.base L j)
    (v : L2C.FactorizationFiber M.base L) :
    ∃ i : Fin 4, v.val = Finsupp.single i (v.val i) ∧ 0 < v.val i := by
  by_cases hvp : 0 < v.val M.base.pivot
  · exact ⟨M.base.pivot,
      pivot_factorization_is_pure_of_killedCount_zero M L hk htail v hvp, hvp⟩
  · have hvpz : v.val M.base.pivot = 0 := by omega
    let u := (tailFiberEquivPivotZero M.base L).symm ⟨v, hvpz⟩
    obtain ⟨j, hupure, huj⟩ :=
      tail_factorization_is_pure_of_three_components M L hL hc u
    have hlift : L2C.tailLift M.base u.val = v.val := by
      have he := congrArg (fun x => x.val.val)
        ((tailFiberEquivPivotZero M.base L).apply_symm_apply ⟨v, hvpz⟩)
      simpa only [tailFiberEquivPivotZero_val] using he
    refine ⟨M.base.order j.succ, ?_, ?_⟩
    · rw [← hlift]
      calc
        L2C.tailLift M.base u.val =
            L2C.tailLift M.base (Finsupp.single j (u.val j)) := congrArg _ hupure
        _ = Finsupp.single (M.base.order j.succ) (u.val j) :=
          tailLift_single M.base j _
        _ = _ := by rw [L3B.tailLift_at_tail]
    · rw [← hlift, L3B.tailLift_at_tail]
      exact huj

theorem full_pure_factorization_unique
    (B : Data Gamma) (L : ℕ) (u v : L2C.FactorizationFiber B L) (i : Fin 4)
    (hupure : u.val = Finsupp.single i (u.val i))
    (hvpure : v.val = Finsupp.single i (v.val i)) : u = v := by
  have huweight : L = u.val i * L2C.weights B i := by
    calc
      L = L2C.weight B u.val := u.property.symm
      _ = L2C.weight B (Finsupp.single i (u.val i)) := congrArg _ hupure
      _ = u.val i * L2C.weights B i := L2C.weight_single B i _
  have hvweight : L = v.val i * L2C.weights B i := by
    calc
      L = L2C.weight B v.val := v.property.symm
      _ = L2C.weight B (Finsupp.single i (v.val i)) := congrArg _ hvpure
      _ = v.val i * L2C.weights B i := L2C.weight_single B i _
  have hcoord : u.val i = v.val i := by
    have hp := L2C.weights_positive B i
    nlinarith
  apply Subtype.ext
  rw [hupure, hvpure, hcoord]

/-- If every point of a positive full fiber is a pure power, then its connected
components, variables, and singleton components all have the same cardinality. -/
theorem full_pure_fiber_cardinalities (B : Data Gamma) (L : ℕ) (_hL : 0 < L)
    (hpure : ∀ u : L2C.FactorizationFiber B L,
      ∃ i : Fin 4, u.val = Finsupp.single i (u.val i) ∧ 0 < u.val i) :
    L2C.componentCount B L = (L2C.fiberVariables B L).card ∧
      L2C.singletonComponentCount B L = (L2C.fiberVariables B L).card := by
  classical
  let role : L2C.FactorizationFiber B L → Fin 4 := fun u => Classical.choose (hpure u)
  have hrole (u : L2C.FactorizationFiber B L) :
      u.val = Finsupp.single (role u) (u.val (role u)) ∧ 0 < u.val (role u) :=
    Classical.choose_spec (hpure u)
  have hrole_inj : Function.Injective role := by
    intro u v he
    exact full_pure_factorization_unique B L u v (role u) (hrole u).1
      ((hrole v).1.trans
        (congrArg (fun i : Fin 4 => Finsupp.single i (v.val i)) he.symm))
  have hgraph : L2C.fiberGraph B L = ⊥ := by
    ext u v
    simp only [SimpleGraph.bot_adj, iff_false]
    rintro ⟨hne, i, hui, hvi⟩
    have hiu : i = role u := by
      by_contra hi
      have hz := congrArg (fun w : Fin 4 →₀ ℕ => w i) (hrole u).1
      simp [Finsupp.single_eq_of_ne hi] at hz
      omega
    have hiv : i = role v := by
      by_contra hi
      have hz := congrArg (fun w : Fin 4 →₀ ℕ => w i) (hrole v).1
      simp [Finsupp.single_eq_of_ne hi] at hz
      omega
    exact hne (hrole_inj (hiu.symm.trans hiv))
  let componentRep : L2C.FiberComponent B L → L2C.FactorizationFiber B L :=
    fun C => Classical.choose C.exists_rep
  have hcomponentRep (C : L2C.FiberComponent B L) :
      (L2C.fiberGraph B L).connectedComponentMk (componentRep C) = C :=
    Classical.choose_spec C.exists_rep
  have hrep_inj : Function.Injective componentRep := by
    intro C E he
    rw [← hcomponentRep C, ← hcomponentRep E, he]
  have hcomponentCard : L2C.componentCount B L =
      Nat.card (L2C.FactorizationFiber B L) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_injective componentRep hrep_inj
    · apply Nat.card_le_card_of_injective (fun u : L2C.FactorizationFiber B L =>
        (L2C.fiberGraph B L).connectedComponentMk u)
      intro u v he
      have hr := SimpleGraph.ConnectedComponent.exact he
      rw [hgraph, SimpleGraph.reachable_bot] at hr
      exact hr
  let toVariable : L2C.FactorizationFiber B L →
      {i : Fin 4 // i ∈ L2C.fiberVariables B L} := fun u =>
    ⟨role u, (L2C.mem_variables B L (role u)).mpr ⟨u, (hrole u).2⟩⟩
  have htoVariable_inj : Function.Injective toVariable := fun u v he =>
    hrole_inj (congrArg Subtype.val he)
  have htoVariable_surj : Function.Surjective toVariable := by
    rintro ⟨i, hi⟩
    obtain ⟨u, hui⟩ := (L2C.mem_variables B L i).mp hi
    have hieq : i = role u := by
      by_contra hne
      have hz := congrArg (fun w : Fin 4 →₀ ℕ => w i) (hrole u).1
      simp [Finsupp.single_eq_of_ne hne] at hz
      omega
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact hieq.symm
  have hfiberCard : Nat.card (L2C.FactorizationFiber B L) =
      (L2C.fiberVariables B L).card := by
    calc
      Nat.card (L2C.FactorizationFiber B L) =
          Nat.card {i : Fin 4 // i ∈ L2C.fiberVariables B L} :=
        Nat.card_congr (Equiv.ofBijective toVariable ⟨htoVariable_inj, htoVariable_surj⟩)
      _ = (L2C.fiberVariables B L).card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_coe _
  have hsingleton (C : L2C.FiberComponent B L) :
      (L2C.componentSupport B L C).card = 1 := by
    let u := componentRep C
    let i := role u
    have hsupp : L2C.componentSupport B L C = {i} := by
      ext a
      constructor
      · intro ha
        obtain ⟨v, hvC, hva⟩ := (L2C.mem_componentSupport B L C a).mp ha
        have hreach : (L2C.fiberGraph B L).Reachable v u :=
          SimpleGraph.ConnectedComponent.exact (hvC.trans (hcomponentRep C).symm)
        rw [hgraph, SimpleGraph.reachable_bot] at hreach
        subst v
        have hz := congrArg (fun w : Fin 4 →₀ ℕ => w a) (hrole u).1
        rw [Finset.mem_singleton]
        by_contra hne
        simp [i, Finsupp.single_eq_of_ne hne] at hz
        omega
      · intro ha
        rw [Finset.mem_singleton] at ha
        subst a
        exact (L2C.mem_componentSupport B L C i).mpr
          ⟨u, hcomponentRep C, (hrole u).2⟩
    simp [hsupp]
  have hsingletonCard : L2C.singletonComponentCount B L =
      L2C.componentCount B L := by
    let e : {C : L2C.FiberComponent B L //
        (L2C.componentSupport B L C).card = 1} ≃ L2C.FiberComponent B L :=
      { toFun := fun C => C.val
        invFun := fun C => ⟨C, hsingleton C⟩
        left_inv := fun C => Subtype.ext rfl
        right_inv := fun _ => rfl }
    exact Nat.card_congr e
  exact ⟨hcomponentCard.trans hfiberCard,
    hsingletonCard.trans (hcomponentCard.trans hfiberCard)⟩

theorem fullPureAt_iff_mem_variables_of_all_pure (B : Data Gamma) (L : ℕ)
    (hpure : ∀ u : L2C.FactorizationFiber B L,
      ∃ i : Fin 4, u.val = Finsupp.single i (u.val i) ∧ 0 < u.val i)
    (i : Fin 4) : FullPureAt B L i ↔ i ∈ L2C.fiberVariables B L := by
  constructor
  · rintro ⟨u, _, hui⟩
    exact (L2C.mem_variables B L i).mpr ⟨u, hui⟩
  · intro hi
    obtain ⟨u, hui⟩ := (L2C.mem_variables B L i).mp hi
    obtain ⟨j, hjpure, hj⟩ := hpure u
    have hij : i = j := by
      by_contra hne
      have hz := congrArg (fun w : Fin 4 →₀ ℕ => w i) hjpure
      simp [Finsupp.single_eq_of_ne hne] at hz
      omega
    subst j
    exact ⟨u, hjpure, hui⟩

/-- Exact full-fiber alternative required by the pure-fiber closure: the three
tail roles occur, every factorization is pure, and the original pivot is the
only optional fourth role. -/
theorem sectorY_full_pure_fiber_dichotomy
    (M : L2B.MultiplicityBase Gamma) (L : ℕ) (hL : 0 < L)
    (hc : L2B.componentCount M.base L = 3)
    (hk : L2B.killedCount M L = 0)
    (htail : ∀ j : Fin 3, TailPureAt M.base L j) :
    (M.base.pivot ∉ L2C.fiberVariables M.base L ∧
      L2C.componentCount M.base L = 3 ∧
      (L2C.fiberVariables M.base L).card = 3 ∧
      L2C.singletonComponentCount M.base L = 3 ∧
      ∀ i : Fin 4, FullPureAt M.base L i ↔ i ≠ M.base.pivot) ∨
    (M.base.pivot ∈ L2C.fiberVariables M.base L ∧
      L2C.componentCount M.base L = 4 ∧
      (L2C.fiberVariables M.base L).card = 4 ∧
      L2C.singletonComponentCount M.base L = 4 ∧
      ∀ i : Fin 4, FullPureAt M.base L i) := by
  classical
  let hpure : ∀ u : L2C.FactorizationFiber M.base L,
      ∃ i : Fin 4, u.val = Finsupp.single i (u.val i) ∧ 0 < u.val i :=
    full_factorization_is_pure_of_sectorY_data M L hL hc hk htail
  have hcards := full_pure_fiber_cardinalities M.base L hL hpure
  have htailmem (j : Fin 3) :
      M.base.order j.succ ∈ L2C.fiberVariables M.base L := by
    exact (fullPureAt_iff_mem_variables_of_all_pure M.base L hpure _).mp
      (tailPureAt_fullPureAt M.base L j (htail j))
  have hnonpivot (i : Fin 4) (hi : i ≠ M.base.pivot) :
      i ∈ L2C.fiberVariables M.base L := by
    obtain ⟨j, rfl⟩ := L3B.exists_tail_index M.base i hi
    exact htailmem j
  by_cases hpivot : M.base.pivot ∈ L2C.fiberVariables M.base L
  · right
    have hvars : L2C.fiberVariables M.base L = Finset.univ := by
      ext i
      simp only [Finset.mem_univ, iff_true]
      by_cases hi : i = M.base.pivot
      · simpa [hi] using hpivot
      · exact hnonpivot i hi
    have hcard : (L2C.fiberVariables M.base L).card = 4 := by simp [hvars]
    refine ⟨hpivot, hcards.1.trans hcard, hcard, hcards.2.trans hcard, ?_⟩
    intro i
    apply (fullPureAt_iff_mem_variables_of_all_pure M.base L hpure i).mpr
    simp [hvars]
  · left
    have hvars : L2C.fiberVariables M.base L =
        (Finset.univ : Finset (Fin 4)).erase M.base.pivot := by
      ext i
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hi hip
        subst i
        exact hpivot hi
      · exact hnonpivot i
    have hcard : (L2C.fiberVariables M.base L).card = 3 := by simp [hvars]
    refine ⟨hpivot, hcards.1.trans hcard, hcard, hcards.2.trans hcard, ?_⟩
    intro i
    rw [fullPureAt_iff_mem_variables_of_all_pure M.base L hpure i, hvars]
    simp

/-- In the three-pure branch the degree `L` saves one unit in the global
four-singleton budget. -/
theorem three_pure_sharpened_load_budget (B : Data Gamma) (L : ℕ)
    (hcomponents : L2C.componentCount B L = 3)
    (hvariables : (L2C.fiberVariables B L).card = 3)
    (hsingletons : L2C.singletonComponentCount B L = 3) :
    ∑ i : Fin 4, L2C.internalLoad B i ≤ 3 := by
  classical
  have hbetti : L2C.Betti B L := by
    unfold L2C.Betti
    omega
  have hLmem : L ∈ L2C.bettiDegrees B :=
    (L2C.mem_bettiDegrees B L).mpr hbetti
  let localLoad : ℕ → ℕ := fun d =>
    (4 - (L2C.fiberVariables B d).card) * (L2C.componentCount B d - 1)
  have hlocalL : localLoad L = 2 := by
    simp [localLoad, hvariables, hcomponents]
  have hother :
      ∑ d ∈ (L2C.bettiDegrees B).erase L, localLoad d ≤
        ∑ d ∈ (L2C.bettiDegrees B).erase L, L2C.singletonComponentCount B d := by
    apply Finset.sum_le_sum
    intro d hd
    exact L2C.local_support_partition_bound B d
      ((L2C.mem_bettiDegrees B d).mp (Finset.mem_of_mem_erase hd))
  have hsingleTotal := L2C.singleton_sum_le_four B (L2C.bettiDegrees B) (by
    intro d hd
    have hb := (L2C.mem_bettiDegrees B d).mp hd
    exact ⟨L2C.betti_positive B d hb, hb⟩)
  have hsingleOther :
      ∑ d ∈ (L2C.bettiDegrees B).erase L, L2C.singletonComponentCount B d ≤ 1 := by
    have hsplit := Finset.sum_erase_add (L2C.bettiDegrees B)
      (L2C.singletonComponentCount B) hLmem
    rw [hsingletons] at hsplit
    omega
  have hlocalTotal : ∑ d ∈ L2C.bettiDegrees B, localLoad d ≤ 3 := by
    have hsplit := Finset.sum_erase_add (L2C.bettiDegrees B) localLoad hLmem
    rw [hlocalL] at hsplit
    omega
  simp_rw [L2C.internalLoad_eq_sum]
  rw [Finset.sum_comm]
  simp_rw [L2C.degree_contribution_identity]
  exact hlocalTotal

theorem four_load_sum_decomposition (B : Data Gamma) :
    (∑ i : Fin 4, L2C.internalLoad B i) =
      L2C.internalLoad B B.pivot +
        ∑ j : Fin 3, L2C.internalLoad B (B.order j.succ) := by
  calc
    (∑ i : Fin 4, L2C.internalLoad B i) =
        ∑ i : Fin 4, L2C.internalLoad B (B.order i) :=
      (Equiv.sum_comp B.order (L2C.internalLoad B)).symm
    _ = L2C.internalLoad B (B.order 0) +
        ∑ j : Fin 3, L2C.internalLoad B (B.order j.succ) :=
      Fin.sum_univ_succ _
    _ = _ := by simp [Data.order]

theorem three_pure_zero_load_tail_role (B : Data Gamma) (L : ℕ)
    (hcomponents : L2C.componentCount B L = 3)
    (hvariables : (L2C.fiberVariables B L).card = 3)
    (hsingletons : L2C.singletonComponentCount B L = 3)
    (hpivotMissing : B.pivot ∉ L2C.fiberVariables B L) :
    ∃ q j : Fin 3, q ≠ j ∧ L2C.internalLoad B (B.order q.succ) = 0 := by
  have hbudget := three_pure_sharpened_load_budget B L
    hcomponents hvariables hsingletons
  have hbetti : L2C.Betti B L := by
    unfold L2C.Betti
    omega
  have hpivotLoad : 2 ≤ L2C.internalLoad B B.pivot := by
    have h := L2C.contribution_le_internalLoad B B.pivot L hbetti hpivotMissing
    rw [hcomponents] at h
    omega
  have htailSum :
      ∑ q : Fin 3, L2C.internalLoad B (B.order q.succ) ≤ 1 := by
    have hsplit := four_load_sum_decomposition B
    omega
  have hpair :
      L2C.internalLoad B (B.order (0 : Fin 3).succ) +
          L2C.internalLoad B (B.order (1 : Fin 3).succ) ≤
        ∑ q : Fin 3, L2C.internalLoad B (B.order q.succ) := by
    have hs : ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have h := Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun q _ _ => L2C.internalLoad_nonneg B (B.order q.succ))
    simpa using h
  by_cases hzero : L2C.internalLoad B (B.order (0 : Fin 3).succ) = 0
  · exact ⟨0, 1, by decide, hzero⟩
  · have hone : L2C.internalLoad B (B.order (1 : Fin 3).succ) = 0 := by omega
    exact ⟨1, 0, by decide, hone⟩

/-- In the four-pure branch the four singleton roles at `L` exhaust the global
singleton budget, so every displayed pivot has zero internal load. -/
theorem four_pure_all_loads_zero (B : Data Gamma) (L : ℕ)
    (hcomponents : L2C.componentCount B L = 4)
    (hvariables : (L2C.fiberVariables B L).card = 4)
    (hsingletons : L2C.singletonComponentCount B L = 4) :
    ∀ i : Fin 4, L2C.internalLoad B i = 0 := by
  classical
  have hLbetti : L2C.Betti B L := by
    unfold L2C.Betti
    omega
  have hLpos : 0 < L := L2C.betti_positive B L hLbetti
  have hvarsUniv : L2C.fiberVariables B L = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using hvariables
  have hsingle_other (d : ℕ) (hd : L2C.Betti B d) (hne : d ≠ L) :
      L2C.singletonComponentCount B d = 0 := by
    have hdpos := L2C.betti_positive B d hd
    have hs := L2C.singleton_sum_le_four B {L, d} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨hLpos, hLbetti⟩
      · exact ⟨hdpos, hd⟩)
    simp [Finset.sum_insert, Ne.symm hne, hsingletons] at hs
    omega
  intro i
  rw [L2C.internalLoad_eq_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hdbetti := (L2C.mem_bettiDegrees B d).mp hd
  have hipresent : i ∈ L2C.fiberVariables B d := by
    by_contra hi
    by_cases hdeq : d = L
    · subst d
      exact hi (by simp [hvarsUniv])
    · have hs0 := hsingle_other d hdbetti hdeq
      have hpart := L2C.local_support_partition_bound B d hdbetti
      have hcard : (L2C.fiberVariables B d).card ≤ 3 := by
        calc
          (L2C.fiberVariables B d).card ≤
              ((Finset.univ : Finset (Fin 4)).erase i).card := by
            apply Finset.card_le_card
            intro x hx
            exact Finset.mem_erase.mpr ⟨fun he => hi (he ▸ hx), Finset.mem_univ x⟩
          _ = 3 := by simp
      have hcomp := hdbetti
      change 2 ≤ L2C.componentCount B d at hcomp
      have hfirst : 0 < 4 - (L2C.fiberVariables B d).card := by omega
      have hsecond : 0 < L2C.componentCount B d - 1 := by omega
      have hproduct := Nat.mul_pos hfirst hsecond
      omega
  simp [hipresent]

/-- Compact actual endpoint for the Y4 worker.  It retains the complete pure
fiber dichotomy, an actual zero-load tail pivot, a distinct second tail pure
power, and field-generic monomiality after repivoting. -/
structure SectorYPureFiberMonomialPivotPackage (P : P2Data Gamma) where
  L : ℕ
  L_pos : 0 < L
  tailComponentCount : L2B.componentCount P.M.base L = 3
  killedCount : L2B.killedCount P.M L = 0
  tailPure : ∀ r : Fin 3, TailPureAt P.M.base L r
  fullDichotomy :
    (P.M.base.pivot ∉ L2C.fiberVariables P.M.base L ∧
      L2C.componentCount P.M.base L = 3 ∧
      (L2C.fiberVariables P.M.base L).card = 3 ∧
      L2C.singletonComponentCount P.M.base L = 3 ∧
      ∀ i : Fin 4, FullPureAt P.M.base L i ↔ i ≠ P.M.base.pivot) ∨
    (P.M.base.pivot ∈ L2C.fiberVariables P.M.base L ∧
      L2C.componentCount P.M.base L = 4 ∧
      (L2C.fiberVariables P.M.base L).card = 4 ∧
      L2C.singletonComponentCount P.M.base L = 4 ∧
      ∀ i : Fin 4, FullPureAt P.M.base L i)
  q : Fin 3
  j : Fin 3
  q_ne_j : q ≠ j
  qPower : L2B.FactorizationFiber P.M.base L
  qPower_pure : qPower.val = Finsupp.single q (qPower.val q)
  qPower_pos : 0 < qPower.val q
  jPower : L2B.FactorizationFiber P.M.base L
  jPower_pure : jPower.val = Finsupp.single j (jPower.val j)
  jPower_pos : 0 < jPower.val j
  zeroLoad : L2C.internalLoad P.M.base (P.M.base.order q.succ) = 0
  monomial : ∀ (k : Type*) [Field k],
    L2B.IsMonomialIdeal k
      ((L2C.atPivot P.M.base (P.M.base.order q.succ)).J k)

/-- Y4 endpoint: actual Sector Y unconditionally supplies a zero-load tail
pivot whose repivoted chosen ideal is monomial, together with a distinct tail
pure power.  No source count at the new pivot is mentioned or identified. -/
theorem sectorY_pure_fiber_monomial_pivot (P : P2Data Gamma)
    (hY : SectorY P.M) : Nonempty (SectorYPureFiberMonomialPivotPackage P) := by
  obtain ⟨L, hL, htailCount, hkilled, htail⟩ :=
    sectorY_tail_three_pure_powers P hY
  have hdich := sectorY_full_pure_fiber_dichotomy P.M L hL htailCount hkilled htail
  rcases hdich with hthree | hfour
  · obtain ⟨q, j, hqj, hqzero⟩ := three_pure_zero_load_tail_role P.M.base L
      hthree.2.1 hthree.2.2.1 hthree.2.2.2.1 hthree.1
    obtain ⟨uq, huqpure, huqpos⟩ := htail q
    obtain ⟨uj, hujpure, hujpos⟩ := htail j
    refine
      ⟨({
          L := L
          L_pos := hL
          tailComponentCount := htailCount
          killedCount := hkilled
          tailPure := htail
          fullDichotomy := Or.inl hthree
          q := q
          j := j
          q_ne_j := hqj
          qPower := uq
          qPower_pure := huqpure
          qPower_pos := huqpos
          jPower := uj
          jPower_pure := hujpure
          jPower_pos := hujpos
          zeroLoad := hqzero
          monomial := ?_ } : SectorYPureFiberMonomialPivotPackage P)⟩
    intro k _
    exact L2C.every_pivot_monomial k P.M.base (P.M.base.order q.succ) hqzero
  · have hzeroAll := four_pure_all_loads_zero P.M.base L
      hfour.2.1 hfour.2.2.1 hfour.2.2.2.1
    let q : Fin 3 := 0
    let j : Fin 3 := 1
    have hqj : q ≠ j := by decide
    have hqzero : L2C.internalLoad P.M.base (P.M.base.order q.succ) = 0 :=
      hzeroAll (P.M.base.order q.succ)
    obtain ⟨uq, huqpure, huqpos⟩ := htail q
    obtain ⟨uj, hujpure, hujpos⟩ := htail j
    refine
      ⟨({
          L := L
          L_pos := hL
          tailComponentCount := htailCount
          killedCount := hkilled
          tailPure := htail
          fullDichotomy := Or.inr hfour
          q := q
          j := j
          q_ne_j := hqj
          qPower := uq
          qPower_pure := huqpure
          qPower_pos := huqpos
          jPower := uj
          jPower_pure := hujpure
          jPower_pos := hujpos
          zeroLoad := hqzero
          monomial := ?_ } : SectorYPureFiberMonomialPivotPackage P)⟩
    intro k _
    exact L2C.every_pivot_monomial k P.M.base (P.M.base.order q.succ) hqzero

end NS25Lean.L5A1
