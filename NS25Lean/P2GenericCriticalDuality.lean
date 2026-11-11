import NS25Lean.P2CriticalFullSignature

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericCriticalDuality
open Classical FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen
  ReturnSourceRigidity ReturnPresentationAdapter PureInternalTransverse CriticalNormalForm
  CriticalShortFibers CriticalCapGeometry CriticalPresentationModes CriticalForwardExchange
  CriticalCapSources CriticalReverseExchange CriticalCapAttainment GenericCriticalCompensation CriticalFullSignature

def family {H : NumericalSemigroup} {B : Base H} {D : Mode B} (F : Front B D) : Set SharedCap.Monomial :=
  tuple '' (Set.range B.norm∪{endpoint D F.mixed})

def additional {H : NumericalSemigroup} {B : Base H} {D : Mode B} (F : Front B D) : Set SharedCap.Monomial :=
  {p | SharedCap.MinimalGenerator (SharedCap.LGenerators (family F) B.C B.u B.v) p ∧
    p∉family F ∧ ∃ g∈family F, 0<g.2.1 ∧ p=SharedCap.Wrap B.u B.v g}

def fullSupport {H : NumericalSemigroup} {B : Base H} {D : Mode B} (F : Front B D) : ℕ :=
  if 0<B.norm B.first 0 ∧ 0<B.norm B.first 1 ∧ 0<B.norm B.first 2 then 1 else 0

def exceptional {H : NumericalSemigroup} {B : Base H} {D : Mode B} (F : Front B D) : Set SharedCap.Monomial :=
  {p | SharedCap.Socle (SharedCap.LGenerators (family F) B.C B.u B.v) p ∧ p.2.1+1=B.C ∧
    SharedCap.Wrap B.u B.v p∉SharedCap.Closure (SharedCap.MGenerators (family F) B.u B.v)}

theorem minimal_zero_original (O : Set SharedCap.Monomial) (C u v : ℕ) (p : SharedCap.Monomial)
    (hp : SharedCap.MinimalGenerator (SharedCap.LGenerators O C u v) p)
    (hz : p∈SharedCap.Closure (SharedCap.ZeroGenerators O)) : p∈O := by
  obtain ⟨g,hg,hle⟩ := hz
  have hgL : g∈SharedCap.Closure (SharedCap.LGenerators O C u v) :=
    ⟨g,Or.inr (Or.inl hg.1),SharedCap.below_refl g⟩
  exact (hp.2 g hgL hle) ▸ hg.1

theorem wrap_redundant_of_all (O : Set SharedCap.Monomial) (C u v : ℕ)
    (hwrap : ∀ g∈O, 0<g.2.1 → SharedCap.Wrap u v g∈SharedCap.Closure (SharedCap.ZeroGenerators O)) :
    {p | SharedCap.MinimalGenerator (SharedCap.LGenerators O C u v) p ∧ p∉O ∧
      ∃ g∈O, 0<g.2.1 ∧ p=SharedCap.Wrap u v g}=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨hp,hn,g,hg,hy,rfl⟩
  exact hn (minimal_zero_original O C u v _ hp (hwrap g hg hy))

theorem family_false {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (hm : F.mixed=false) : family F=originals B := by
  cases D <;> simp [family,originals,endpoint,hm,Base.originals]

theorem endpoint_c_covered {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : tuple (vector 0 0 B.L)∈SharedCap.Closure (SharedCap.ZeroGenerators (family F)) := by
  cases D with
  | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
    cases hm : F.mixed with
    | false =>
      refine ⟨tuple (vector 0 0 B.L),⟨?_,by simp [tuple]⟩,SharedCap.below_refl _⟩
      exact ⟨vector 0 0 B.L,Or.inr (by simp [endpoint,hm]),rfl⟩
    | true =>
      have hb : (B.L-1)*B.triple.g 2∈B.K ∧
          B.triple.weight (vector (w-1) z 0)∉B.K ∧ B.triple.weight (vector w (z-1) 0)∉B.K := by
        simpa [boundaryGuards,hm] using F.boundary
      obtain ⟨s,a,ha,haL,hs⟩ := pure_c_source B hb.1
      refine ⟨tuple (B.norm s),⟨⟨B.norm s,Or.inl ⟨s,rfl⟩,rfl⟩,by simp [tuple,hs]⟩,?_⟩
      simp [SharedCap.Below,tuple,hs]
      omega
  | purePair hpair =>
    refine ⟨tuple (vector 0 0 B.L),⟨?_,by simp [tuple]⟩,SharedCap.below_refl _⟩
    exact ⟨vector 0 0 B.L,Or.inr rfl,rfl⟩

theorem N_to_family {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) {x z : ℕ} (hN : B.N x z) :
    (x,0,z)∈SharedCap.Closure (SharedCap.ZeroGenerators (family F)) := by
  obtain ⟨g,hg,hle⟩ := hN
  have ht : SharedCap.Below (tuple g) (x,0,z) := by
    exact ⟨by simpa [tuple] using hle 0,by simpa [tuple] using hle 1,by simpa [tuple] using hle 2⟩
  rcases hg.1 with ⟨s,rfl⟩ | rfl
  · exact ⟨tuple (B.norm s),⟨⟨B.norm s,Or.inl ⟨s,rfl⟩,rfl⟩,hg.2⟩,ht⟩
  · exact SharedCap.closure_upward (endpoint_c_covered F) ht

theorem endpoint_wrap_redundant {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (hy : 0<endpoint D F.mixed 1) :
    SharedCap.Wrap B.u B.v (tuple (endpoint D F.mixed))∈
      SharedCap.Closure (SharedCap.ZeroGenerators (family F)) := by
  cases D with
  | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
    cases hm : F.mixed with
    | false => simp [endpoint,hm] at hy
    | true =>
      obtain ⟨s,a,ha,haR,hs⟩ := B.axis_source F.axis_killed
      refine ⟨tuple (B.norm s),⟨⟨B.norm s,Or.inl ⟨s,rfl⟩,rfl⟩,by simp [tuple,hs]⟩,?_⟩
      simp [SharedCap.Below,SharedCap.Wrap,tuple,endpoint,hm,hs]
      omega
  | purePair hpair => simp [endpoint] at hy

theorem all_wraps_redundant_of_first_y_zero {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (hzero : B.norm B.first 1=0) :
    ∀ g∈family F, 0<g.2.1 → SharedCap.Wrap B.u B.v g∈
      SharedCap.Closure (SharedCap.ZeroGenerators (family F)) := by
  rintro g ⟨e,he,rfl⟩ hy
  rcases he with ⟨s,rfl⟩ | rfl
  · have hnf : s≠B.first := by intro h; simp [tuple,h,hzero] at hy
    have hbounds := F.coefficient_bounds
    have hshape := normal_nonfirst_positive_y_shape B F.pure_b_live s hnf hy
    apply N_to_family F
    rcases hshape with h | h
    · exact B.N_upward (xy_strict_original_core B F.axis_killed hbounds.2 D
        (SharedTail.mode_genuine D) s hnf h.1 hy) le_rfl (by have := B.v_pos; omega)
    · exact B.N_upward (yz_strict_original_core B hbounds.1 D
        (SharedTail.mode_genuine D) s hnf hy h.2) (by have := B.u_pos; omega) le_rfl
  · exact endpoint_wrap_redundant F hy

theorem zero_case {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (hzero : B.norm B.first 1=0) :
    additional F=∅ ∧ fullSupport F=0 := by
  exact ⟨wrap_redundant_of_all (family F) B.C B.u B.v
    (all_wraps_redundant_of_first_y_zero F hzero),by simp [fullSupport,hzero]⟩

def remainingSignature {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (hy : 0<B.norm B.first 1) : Signature B D where
  axis_killed := F.axis_killed
  boundary_cut := by
    obtain ⟨p,hp,g,hg,_,he⟩ := F.boundary_degree_proper
    exact he ▸ ErasedSourceScreen.cut_add H hp hg
  v_lt := F.coefficient_bounds.2
  neck_uncut := by
    intro hk
    have := F.internal_cut_first_y_zero hk
    omega
  first_y_pos := hy
  pure_b_live := F.pure_b_live
  pure_c_live := by
    have hm : F.mixed=false := by
      cases hm : F.mixed with
      | false => rfl
      | true => have := F.mixed_first_y_zero hm; omega
    cases D with
    | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
      have hb : (B.L-1)*B.triple.g 2∉B.K ∧
          boundaryKilled (.positive p q w z hp hq hw hz hR hC hL hcenter hboundary : Mode B) := by
        simpa [boundaryGuards,hm] using F.boundary
      exact hb.1
    | purePair hpair => exact F.boundary.2
  boundary_killed := by
    have hm : F.mixed=false := by
      cases hm : F.mixed with
      | false => rfl
      | true => have := F.mixed_first_y_zero hm; omega
    cases D with
    | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
      have hb : (B.L-1)*B.triple.g 2∉B.K ∧
          boundaryKilled (.positive p q w z hp hq hw hz hR hC hL hcenter hboundary : Mode B) := by
        simpa [boundaryGuards,hm] using F.boundary
      exact hb.2
    | purePair hpair => trivial
  inactive_killed := F.inactive_killed

/-- Generic critical-return duality, including both actual zero branches.
True critical exponents and predecessor signs produce the cap data; the
critical mode itself proves genuine presentation over every field. -/
theorem compensation {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : (additional F).ncard+fullSupport F≤(exceptional F).ncard := by
  by_cases hz : B.norm B.first 1=0
  · obtain ⟨ha,hf⟩ := zero_case F hz
    simp [ha,hf]
  · have hy : 0<B.norm B.first 1 := Nat.pos_of_ne_zero hz
    have hm : F.mixed=false := by
      cases hm : F.mixed with
      | false => rfl
      | true => have := F.mixed_first_y_zero hm; omega
    let G := remainingSignature F hy
    let A := capData B D G (SharedTail.mode_genuine D)
    have hO : A.originals=family F := (family_false F hm).symm
    have hAdd : additional F=A.additionalWraps := by
      simp only [additional,SharedCap.Data.additionalWraps,hO]
      rfl
    have hExc : exceptional F=A.exceptional := by
      simp only [exceptional,SharedCap.Data.exceptional,hO]
      rfl
    have hFull : fullSupport F=A.fullSupport := by
      simp only [fullSupport,SharedCap.Data.fullSupport]
      change (if 0<B.norm B.first 0 ∧ 0<B.norm B.first 1 ∧ 0<B.norm B.first 2 then 1 else 0)=
        if 0<B.norm B.first 0 ∧ 0<B.norm B.first 2 then 1 else 0
      simp only [hy,true_and]
    rw [hAdd,hExc,hFull]
    exact SharedCap.compensation A

theorem nonfirst_wrap_in_original_zero_ideal {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (s : B.Source) (hnf : s≠B.first) (hy : 0<B.norm s 1) :
    SharedCap.Wrap B.u B.v (tuple (B.norm s))∈SharedCap.Closure (SharedCap.ZeroGenerators (family F)) := by
  apply N_to_family F
  rcases normal_nonfirst_positive_y_shape B F.pure_b_live s hnf hy with h | h
  · exact B.N_upward (xy_strict_original_core B F.axis_killed F.coefficient_bounds.2 D
      (SharedTail.mode_genuine D) s hnf h.1 hy) le_rfl (by have := B.v_pos; omega)
  · exact B.N_upward (yz_strict_original_core B F.coefficient_bounds.1 D
      (SharedTail.mode_genuine D) s hnf hy h.2) (by have := B.u_pos; omega) le_rfl

theorem internal_cut_zero {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (hk : B.C*B.triple.g 1∈B.K) : additional F=∅ ∧ fullSupport F=0 :=
  zero_case F (F.internal_cut_first_y_zero hk)

theorem mixed_alive_zero {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) (hm : F.mixed=true) : additional F=∅ ∧ fullSupport F=0 :=
  zero_case F (F.mixed_first_y_zero hm)

theorem family_finite {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : (family F).Finite := by
  letI := source_finite B
  exact ((Set.finite_range B.norm).union (Set.finite_singleton _)).image tuple

theorem additional_finite {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : (additional F).Finite := by
  apply ((family_finite F).image (SharedCap.Wrap B.u B.v)).subset
  rintro p ⟨_,_,g,hg,_,rfl⟩
  exact ⟨g,hg,rfl⟩

theorem exceptional_bounds {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) {p : SharedCap.Monomial} (hp : p∈exceptional F) :
    p.1<B.R ∧ p.2.1<B.C ∧ p.2.2<B.L := by
  have hn := hp.1.1
  have hx : p.1<B.R := by
    obtain ⟨s,a,ha,haR,hs⟩ := B.axis_source F.axis_killed
    by_contra h
    exact hn ⟨tuple (B.norm s),Or.inr (Or.inl ⟨B.norm s,Or.inl ⟨s,rfl⟩,rfl⟩),
      by simp [SharedCap.Below,tuple,hs]; omega⟩
  have hy : p.2.1<B.C := by
    by_contra h
    exact hn ⟨(0,B.C,0),Or.inl rfl,by simp [SharedCap.Below]; omega⟩
  have hz : p.2.2<B.L := by
    by_contra h
    have hcl := SharedCap.closure_upward (endpoint_c_covered F)
      (show SharedCap.Below (tuple (vector 0 0 B.L)) p by simp [SharedCap.Below,tuple]; omega)
    obtain ⟨g,hg,hle⟩ := hcl
    exact hn ⟨g,Or.inr (Or.inl hg.1),hle⟩
  exact ⟨hx,hy,hz⟩

theorem exceptional_finite {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : (exceptional F).Finite := by
  let S := ((Finset.range B.R).product ((Finset.range B.C).product (Finset.range B.L)))
  apply S.finite_toSet.subset
  intro p hp
  have h := exceptional_bounds F hp
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr h.1,
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr h.2.1,Finset.mem_range.mpr h.2.2⟩⟩

def fullSource {H : NumericalSemigroup} (B : Base H) (s : B.Source) : Prop :=
  0<B.norm s 0 ∧ 0<B.norm s 1 ∧ 0<B.norm s 2

theorem full_source_eq_first {H : NumericalSemigroup} (B : Base H) (s : B.Source)
    (hs : fullSource B s) : s=B.first := by
  apply Subtype.ext
  apply full_support_source_is_first B.triple B.m B.m_pos s
  intro i
  rw [←B.norm_degree s]
  apply B.triple.D_of_coordinate
  fin_cases i <;> first | exact hs.1 | exact hs.2.1 | exact hs.2.2

theorem fullSupport_source_count {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : fullSupport F=Nat.card {s : B.Source //
      0<B.norm s 0 ∧ 0<B.norm s 1 ∧ 0<B.norm s 2} := by
  let A := {s : B.Source // fullSource B s}
  letI : Subsingleton A := ⟨fun s t => Subtype.ext
    ((full_source_eq_first B s.val s.property).trans (full_source_eq_first B t.val t.property).symm)⟩
  unfold fullSupport
  split_ifs with hf
  · exact (Nat.card_of_subsingleton (⟨B.first,hf⟩ : A)).symm
  · have hEmpty : IsEmpty A := ⟨fun s => hf ((full_source_eq_first B s.val s.property) ▸ s.property)⟩
    exact (Nat.card_eq_zero.mpr (Or.inl hEmpty)).symm

def fullOriginals {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : Set SharedCap.Monomial :=
  {g∈family F | 0<g.1 ∧ 0<g.2.1 ∧ 0<g.2.2}

theorem norm_injective {H : NumericalSemigroup} (B : Base H) : Function.Injective B.norm := by
  intro s t h
  apply Subtype.ext
  rw [←B.norm_degree s,←B.norm_degree t,h]

theorem fullSupport_original_count {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : fullSupport F=(fullOriginals F).ncard := by
  rw [fullSupport_source_count F]
  let f : {s : B.Source // fullSource B s}→fullOriginals F := fun s =>
    ⟨tuple (B.norm s.val),⟨⟨B.norm s.val,Or.inl ⟨s.val,rfl⟩,rfl⟩,s.property⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s t h
      apply Subtype.ext
      apply norm_injective B
      apply tuple_injective
      exact congrArg Subtype.val h
    · rintro ⟨g,⟨⟨e,he,rfl⟩,hg⟩⟩
      rcases he with ⟨s,rfl⟩ | rfl
      · exact ⟨⟨s,hg⟩,rfl⟩
      · have hn : ∀ (D : Mode B) (b : Bool), ¬(0<(tuple (endpoint D b)).1 ∧
            0<(tuple (endpoint D b)).2.1 ∧ 0<(tuple (endpoint D b)).2.2) := by
          intro D b
          cases D <;> cases b <;> simp [endpoint,tuple]
        exact (hn D F.mixed hg).elim
  exact Nat.card_congr (Equiv.ofBijective f hf)

/-- The literal normalized source-count version, with no presentation input. -/
theorem compensation_source_count {H : NumericalSemigroup} {B : Base H} {D : Mode B}
    (F : Front B D) : (additional F).ncard+Nat.card {s : B.Source //
      0<B.norm s 0 ∧ 0<B.norm s 1 ∧ 0<B.norm s 2}≤(exceptional F).ncard := by
  rw [←fullSupport_source_count F]
  exact compensation F

end NS25Lean.GenericCriticalDuality
