import NS25Lean.OneDefectFrontend
import Mathlib.Data.Int.Interval

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B
variable {Gamma : NumericalSemigroup}

/-- A translated presentation relation, in either orientation, of the unique tie. -/
def TieStep {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (u v : Fin 3 →₀ ℕ) : Prop :=
  ∃ t : Fin 3 →₀ ℕ,
    (u = t + N.alpha.val ∧ v = t + N.beta.val) ∨
    (u = t + N.beta.val ∧ v = t + N.alpha.val)

/-- A finite presentation path all of whose steps translate the actual unique tie. -/
abbrev TiePath {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) :=
  Relation.ReflTransGen (TieStep N)

theorem tieStep_add {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    {u v : Fin 3 →₀ ℕ} (huv : TieStep N u v) (w : Fin 3 →₀ ℕ) :
    TieStep N (w + u) (w + v) := by
  rcases huv with ⟨t, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨w + t, Or.inl ⟨(add_assoc _ _ _).symm, (add_assoc _ _ _).symm⟩⟩
  · exact ⟨w + t, Or.inr ⟨(add_assoc _ _ _).symm, (add_assoc _ _ _).symm⟩⟩

theorem tiePath_add {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    {u v : Fin 3 →₀ ℕ} (huv : TiePath N u v) (w : Fin 3 →₀ ℕ) :
    TiePath N (w + u) (w + v) :=
  huv.lift (fun t => w + t) (fun _ _ ht => tieStep_add N ht w)

/-- Appendix A presentation paths in the actual Apéry region. Shared-factor graph
edges reduce to smaller Apéry degrees, so no general presentation is postulated. -/
theorem apery_presentation_paths {k : Type*} [Field k] {M : MultiplicityBase Gamma}
    {h : ℕ} (F : InternalFrontend k M h) (d : ℕ) (hd : d ∈ M.base.apery)
    (u v : FactorizationFiber M.base d) : TiePath F.normal u.val v.val := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases he : d = h
    · subst d
      rcases F.normal.exactly_two u with rfl | rfl <;>
        rcases F.normal.exactly_two v with rfl | rfl
      · exact .refl
      · exact .single ⟨0, Or.inl ⟨by simp, by simp⟩⟩
      · exact .single ⟨0, Or.inr ⟨by simp, by simp⟩⟩
      · exact .refl
    · have hc := apery_component_le_one M d (F.unique_degree.2 d he) hd
      let := Fintype.ofFinite (FiberComponent M.base d)
      have : Subsingleton (FiberComponent M.base d) :=
        Fintype.card_le_one_iff_subsingleton.mp (by
          simpa only [componentCount, Nat.card_eq_fintype_card] using hc)
      have hr : (fiberGraph M.base d).Reachable u v :=
        SimpleGraph.ConnectedComponent.exact (Subsingleton.elim _ _)
      have hp := (SimpleGraph.reachable_iff_reflTransGen u v).mp hr
      apply hp.lift' Subtype.val
      intro s t hst
      rcases hst with ⟨_, j, hs, ht⟩
      have hes := removed_weight M.base d s j hs
      have het := removed_weight M.base d t j ht
      have hw := weights_positive M.base j
      let s' : FactorizationFiber M.base (d - weights M.base j) :=
        ⟨s.val - Finsupp.single j 1, by omega⟩
      let t' : FactorizationFiber M.base (d - weights M.base j) :=
        ⟨t.val - Finsupp.single j 1, by omega⟩
      have hi := ih (d - weights M.base j) (by omega)
        (apery_remove M.base d hd s j hs) s' t'
      have hl := tiePath_add F.normal hi (Finsupp.single j 1)
      simpa only [s', t', remove_variable_add s.val j hs,
        remove_variable_add t.val j ht] using hl

/-- The exponent difference of the actual normalized tie, with integer coordinates. -/
def tieDelta {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) (i : Fin 3) : ℤ :=
  (N.alpha.val i : ℤ) - (N.beta.val i : ℤ)

theorem tieDelta_x {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) :
    tieDelta N (N.perm 0) = N.a := by
  simp [tieDelta, N.alpha_eq, N.beta_eq, N.perm.injective.eq_iff]

theorem tieDelta_y {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) :
    tieDelta N (N.perm 1) = -(N.b : ℤ) := by
  simp [tieDelta, N.alpha_eq, N.beta_eq, N.perm.injective.eq_iff]

theorem tieDelta_z {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) :
    tieDelta N (N.perm 2) = -(N.c : ℤ) := by
  simp [tieDelta, N.alpha_eq, N.beta_eq, N.perm.injective.eq_iff]

theorem tieStep_integer_difference {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    {u v : Fin 3 →₀ ℕ} (huv : TieStep N u v) :
    ∃ j : ℤ, ∀ i, (v i : ℤ) = (u i : ℤ) + j * tieDelta N i := by
  rcases huv with ⟨t, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · refine ⟨-1, fun i => ?_⟩
    simp only [Finsupp.add_apply, Nat.cast_add, tieDelta]
    ring
  · refine ⟨1, fun i => ?_⟩
    simp only [Finsupp.add_apply, Nat.cast_add, tieDelta]
    ring

theorem tiePath_integer_difference {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    {u v : Fin 3 →₀ ℕ} (huv : TiePath N u v) :
    ∃ j : ℤ, ∀ i, (v i : ℤ) = (u i : ℤ) + j * tieDelta N i := by
  induction huv with
  | refl => exact ⟨0, by simp⟩
  | @tail v w _ hvw ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨l, hl⟩ := tieStep_integer_difference N hvw
    refine ⟨j + l, fun i => ?_⟩
    rw [hl, hj]
    ring

/-- All actual factorizations of an Apéry degree differ by an integer tie multiple. -/
theorem apery_factorization_difference {k : Type*} [Field k]
    {M : MultiplicityBase Gamma} {h : ℕ} (F : InternalFrontend k M h)
    (d : ℕ) (hd : d ∈ M.base.apery) (u v : FactorizationFiber M.base d) :
    ∃ j : ℤ, ∀ i, (v.val i : ℤ) = (u.val i : ℤ) + j * tieDelta F.normal i :=
  tiePath_integer_difference F.normal (apery_presentation_paths F d hd u v)

theorem affine_tie_weight {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (u v : Fin 3 →₀ ℕ) (j : ℤ)
    (hv : ∀ i, (v i : ℤ) = (u i : ℤ) + j * tieDelta N i) :
    weight B v = weight B u := by
  have he : (weight B v : ℤ) = (weight B u : ℤ) +
      j * ((weight B N.alpha.val : ℤ) - (weight B N.beta.val : ℤ)) := by
    simp only [weight_eq_sum, Nat.cast_sum, Nat.cast_mul]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hv]
    unfold tieDelta
    ring
  rw [N.alpha.property, N.beta.property, sub_self, mul_zero, add_zero] at he
  exact_mod_cast he

/-- Every intermediate point of a presentation path has the same actual degree. -/
theorem tiePath_weight {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    {u v : Fin 3 →₀ ℕ} (huv : TiePath N u v) : weight B v = weight B u := by
  obtain ⟨j, hj⟩ := tiePath_integer_difference N huv
  exact affine_tie_weight N u v j hj

theorem tie_parameter_unique {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (u v : Fin 3 →₀ ℕ) {j l : ℤ}
    (hj : ∀ i, (v i : ℤ) = (u i : ℤ) + j * tieDelta N i)
    (hl : ∀ i, (v i : ℤ) = (u i : ℤ) + l * tieDelta N i) : j = l := by
  have hx := hj (N.perm 0)
  have hy := hl (N.perm 0)
  rw [tieDelta_x] at hx hy
  have ha : (N.a : ℤ) ≠ 0 := by have := N.a_ge_two; omega
  exact mul_right_cancel₀ ha (by linarith : j * (N.a : ℤ) = l * (N.a : ℤ))

/-- Nonnegativity is the only restriction on an integer parameter along the tie. -/
def TieAdmissible {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (u : Fin 3 →₀ ℕ) (j : ℤ) : Prop :=
  ∀ i, 0 ≤ (u i : ℤ) + j * tieDelta N i

theorem tieAdmissible_zero {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (u : Fin 3 →₀ ℕ) : TieAdmissible N u 0 := by
  intro i
  simp

theorem tieAdmissible_nonneg_of_slab {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (u : Fin 3 →₀ ℕ) (hu : u (N.perm 0) < N.a) {j : ℤ}
    (hj : TieAdmissible N u j) : 0 ≤ j := by
  have hx := hj (N.perm 0)
  rw [tieDelta_x] at hx
  have hc : (u (N.perm 0) : ℤ) < N.a := by exact_mod_cast hu
  by_contra hn
  have hneg : j ≤ -1 := by omega
  have hm := mul_le_mul_of_nonneg_right hneg (Int.natCast_nonneg N.a)
  linarith

theorem tieAdmissible_bound {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    {d : ℕ} (u : FactorizationFiber B d) {j : ℤ} (hj : TieAdmissible N u.val j) :
    -(d : ℤ) ≤ j ∧ j ≤ (d : ℤ) := by
  have hx := hj (N.perm 0)
  have hy := hj (N.perm 1)
  rw [tieDelta_x] at hx
  rw [tieDelta_y] at hy
  have hux : (u.val (N.perm 0) : ℤ) ≤ d := by
    exact_mod_cast fiber_coordinate_le B d u (N.perm 0)
  have huy : (u.val (N.perm 1) : ℤ) ≤ d := by
    exact_mod_cast fiber_coordinate_le B d u (N.perm 1)
  have ha : (1 : ℤ) ≤ N.a := by have := N.a_ge_two; omega
  have hb : (1 : ℤ) ≤ N.b := by exact_mod_cast N.b_positive
  by_cases hpos : 0 ≤ j
  · refine ⟨by omega, ?_⟩
    have hm := mul_nonneg hpos (sub_nonneg.mpr hb)
    nlinarith
  · refine ⟨?_, by omega⟩
    have hm := mul_nonneg (neg_nonneg.mpr (le_of_lt (lt_of_not_ge hpos)))
      (sub_nonneg.mpr ha)
    nlinarith

theorem tieAdmissible_between {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (u : Fin 3 →₀ ℕ) {l j r : ℤ} (hl : TieAdmissible N u l)
    (hr : TieAdmissible N u r) (hlj : l ≤ j) (hjr : j ≤ r) :
    TieAdmissible N u j := by
  intro i
  by_cases hp : 0 ≤ tieDelta N i
  · have hm := mul_le_mul_of_nonneg_right hlj hp
    have := hl i
    linarith
  · have hm := mul_le_mul_of_nonpos_right hjr (le_of_lt (lt_of_not_ge hp))
    have := hr i
    linarith

theorem tieAdmissible_realized {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    {d : ℕ} (u : FactorizationFiber B d) {j : ℤ} (hj : TieAdmissible N u.val j) :
    ∃ v : FactorizationFiber B d,
      ∀ i, (v.val i : ℤ) = (u.val i : ℤ) + j * tieDelta N i := by
  let v : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun i => ((u.val i : ℤ) + j * tieDelta N i).toNat)
  have hv : ∀ i, (v i : ℤ) = (u.val i : ℤ) + j * tieDelta N i := by
    intro i
    change (((u.val i : ℤ) + j * tieDelta N i).toNat : ℤ) = _
    exact Int.toNat_of_nonneg (hj i)
  refine ⟨⟨v, (affine_tie_weight N u.val v j hv).trans u.property⟩, hv⟩

/-- The exact finite interval of all nonnegative points on a tie line. -/
theorem tie_admissible_interval {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    {d : ℕ} (u : FactorizationFiber B d) :
    ∃ l r : ℤ, l ≤ r ∧ ∀ j : ℤ, TieAdmissible N u.val j ↔ l ≤ j ∧ j ≤ r := by
  classical
  let s := (Finset.Icc (-(d : ℤ)) (d : ℤ)).filter (TieAdmissible N u.val)
  have hs : ∀ j : ℤ, j ∈ s ↔ TieAdmissible N u.val j := by
    intro j
    simp only [s, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨And.right, fun hj => ⟨tieAdmissible_bound N u hj, hj⟩⟩
  have hn : s.Nonempty := ⟨0, (hs 0).mpr (tieAdmissible_zero N u.val)⟩
  refine ⟨s.min' hn, s.max' hn, s.min'_le_max' hn, fun j => ?_⟩
  constructor
  · intro hj
    exact ⟨s.min'_le j ((hs j).mpr hj), s.le_max' j ((hs j).mpr hj)⟩
  · rintro ⟨hl, hr⟩
    exact tieAdmissible_between N u.val
      ((hs _).mp (s.min'_mem hn)) ((hs _).mp (s.max'_mem hn)) hl hr


/-- One finite-interval engine for every fiber governed by a principal tie. -/
theorem fiber_chain_of_difference {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (d : ℕ) (hdH : d ∈ B.H)
    (hdiff : ∀ u v : FactorizationFiber B d,
      ∃ j : ℤ, ∀ i, (v.val i : ℤ) = (u.val i : ℤ)+j*tieDelta N i) :
    ∃ u₀ : FactorizationFiber B d, ∃ l r : ℤ, l ≤ r ∧
      (∀ v : FactorizationFiber B d, ∃ j : ℤ, l ≤ j ∧ j ≤ r ∧
        ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ)+j*tieDelta N i) ∧
      (∀ j : ℤ, l ≤ j → j ≤ r → ∃ v : FactorizationFiber B d,
        ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ)+j*tieDelta N i) := by
  obtain ⟨u₀⟩ := fiber_nonempty B ⟨d,hdH⟩
  obtain ⟨l,r,hlr,hi⟩ := tie_admissible_interval N u₀
  refine ⟨u₀,l,r,hlr,?_,?_⟩
  · intro v
    obtain ⟨j,hj⟩ := hdiff u₀ v
    have ha : TieAdmissible N u₀.val j := by
      intro i;rw [←hj i];exact Int.natCast_nonneg _
    exact ⟨j,((hi j).mp ha).1,((hi j).mp ha).2,hj⟩
  · intro j hl hr
    exact tieAdmissible_realized N u₀ ((hi j).mpr ⟨hl,hr⟩)

theorem normalized_fiber_chain_of_difference (k : Type*) [Field k]
    {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) (d : ℕ) (hdH : d ∈ B.H)
    (hdiff : ∀ u v : FactorizationFiber B d,
      ∃ j : ℤ, ∀ i, (v.val i : ℤ) = (u.val i : ℤ)+j*tieDelta N i) :
    ∃ u₀ : FactorizationFiber B d, u₀.val (N.perm 0) < N.a ∧
      ∃ r : ℤ, 0 ≤ r ∧
        (∀ v : FactorizationFiber B d, ∃! j : ℤ, 0 ≤ j ∧ j ≤ r ∧
          ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ)+j*tieDelta N i) ∧
        (∀ j : ℤ, 0 ≤ j → j ≤ r → ∃ v : FactorizationFiber B d,
          ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ)+j*tieDelta N i) := by
  obtain ⟨u⟩ := fiber_nonempty B ⟨d,hdH⟩
  obtain ⟨v₀,hv₀,hdeg,_⟩ := N.normalize_monomial k u.val
  let u₀ : FactorizationFiber B d := ⟨v₀,hdeg.trans u.property⟩
  obtain ⟨l,r,hlr,hi⟩ := tie_admissible_interval N u₀
  have hl0 : l=0 := by
    apply le_antisymm
    · exact ((hi 0).mp (tieAdmissible_zero N u₀.val)).1
    · exact tieAdmissible_nonneg_of_slab N u₀.val hv₀ ((hi l).mpr ⟨le_rfl,hlr⟩)
  subst l
  refine ⟨u₀,hv₀,r,hlr,?_,?_⟩
  · intro v
    obtain ⟨j,hj⟩ := hdiff u₀ v
    have ha : TieAdmissible N u₀.val j := by
      intro i;rw [←hj i];exact Int.natCast_nonneg _
    refine ⟨j,⟨((hi j).mp ha).1,((hi j).mp ha).2,hj⟩,?_⟩
    intro l hl
    exact tie_parameter_unique N u₀.val v.val hl.2.2 hj
  · intro j hl hr
    exact tieAdmissible_realized N u₀ ((hi j).mpr ⟨hl,hr⟩)

theorem slab_unique_of_integer_difference {B : Data Gamma} {h d : ℕ}
    (N : TieNormalForm B h) (u v : FactorizationFiber B d)
    (hdiff : ∃ j : ℤ, ∀ i, (v.val i : ℤ)=(u.val i : ℤ)+j*tieDelta N i)
    (hu : u.val (N.perm 0) < N.a) (hv : v.val (N.perm 0) < N.a) : u=v := by
  obtain ⟨j,hj⟩:=hdiff
  have had : TieAdmissible N u.val j := by
    intro i;rw [←hj i];exact Int.natCast_nonneg _
  have hn := tieAdmissible_nonneg_of_slab N u.val hu had
  have hjle : j ≤ 0 := by
    by_contra hnot
    have hjpos : 1 ≤ j := by omega
    have hm := mul_le_mul_of_nonneg_right hjpos (Int.natCast_nonneg N.a)
    have hx := hj (N.perm 0)
    rw [tieDelta_x] at hx
    have hv' : (v.val (N.perm 0) : ℤ) < N.a := by exact_mod_cast hv
    have hu' := Int.natCast_nonneg (u.val (N.perm 0))
    nlinarith
  have hz : j=0 := by omega
  apply Subtype.ext;ext i
  have he := hj i
  simp only [hz,zero_mul,add_zero] at he
  exact_mod_cast he.symm

/-- Appendix A factorization-chain theorem: every actual Apéry factorization is
one point of a finite integer interval along delta, and every point in that interval
is an actual factorization. Both directions include the original semigroup degree. -/
theorem apery_factorization_chain {k : Type*} [Field k]
    {M : MultiplicityBase Gamma} {h : ℕ} (F : InternalFrontend k M h)
    (d : ℕ) (hd : d ∈ M.base.apery) :
    ∃ u₀ : FactorizationFiber M.base d, ∃ l r : ℤ, l ≤ r ∧
      (∀ v : FactorizationFiber M.base d,
        ∃ j : ℤ, l ≤ j ∧ j ≤ r ∧
          ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ) + j * tieDelta F.normal i) ∧
      (∀ j : ℤ, l ≤ j → j ≤ r →
        ∃ v : FactorizationFiber M.base d,
          ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ) + j * tieDelta F.normal i) := by
  exact fiber_chain_of_difference F.normal d (M.base.apery_eq_compl ▸ hd).1
    (fun u v=>apery_factorization_difference F d hd u v)

/-- A normalized version of the same chain: the base lies in the actual x-slab,
the first integer parameter is zero, and each actual factorization has one parameter. -/
theorem apery_normalized_factorization_chain {k : Type*} [Field k]
    {M : MultiplicityBase Gamma} {h : ℕ} (F : InternalFrontend k M h)
    (d : ℕ) (hd : d ∈ M.base.apery) :
    ∃ u₀ : FactorizationFiber M.base d, u₀.val (F.normal.perm 0) < F.normal.a ∧
      ∃ r : ℤ, 0 ≤ r ∧
        (∀ v : FactorizationFiber M.base d,
          ∃! j : ℤ, 0 ≤ j ∧ j ≤ r ∧
            ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ) + j * tieDelta F.normal i) ∧
        (∀ j : ℤ, 0 ≤ j → j ≤ r →
          ∃ v : FactorizationFiber M.base d,
            ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ) + j * tieDelta F.normal i) := by
  exact normalized_fiber_chain_of_difference k F.normal d (M.base.apery_eq_compl ▸ hd).1
    (fun u v=>apery_factorization_difference F d hd u v)

end NS25Lean.L3C
