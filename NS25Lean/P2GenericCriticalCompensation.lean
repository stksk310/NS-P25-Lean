import NS25Lean.P2CriticalCapAttainment
import NS25Lean.AttainedCapCompensation

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericCriticalCompensation
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen ReturnSourceRigidity
  PureInternalTransverse CriticalNormalForm CriticalShortFibers CriticalCapGeometry
  CriticalPresentationModes CriticalForwardExchange CriticalCapSources CriticalReverseExchange CriticalCapAttainment

def tuple (e : Exponent) : SharedCap.Monomial := (e 0,e 1,e 2)
@[simp] theorem tuple_vector (x y z : ℕ) : tuple (vector x y z)=(x,y,z) := by simp [tuple]

theorem tuple_injective : Function.Injective tuple := by
  intro e f h
  have h0 := congrArg (fun p : SharedCap.Monomial => p.1) h
  have h1 := congrArg (fun p : SharedCap.Monomial => p.2.1) h
  have h2 := congrArg (fun p : SharedCap.Monomial => p.2.2) h
  ext i
  fin_cases i <;> assumption

def originals {H : NumericalSemigroup} (B : Base H) : Set SharedCap.Monomial := tuple '' B.originals

theorem source_finite {H : NumericalSemigroup} (B : Base H) : Finite B.Source := by
  have h := return_sources_finite H B.m Set.univ
  simpa only [Sources,returnCut_univ] using h

theorem originals_finite {H : NumericalSemigroup} (B : Base H) : (originals B).Finite := by
  letI := source_finite B
  exact ((Set.finite_range B.norm).union (Set.finite_singleton _)).image tuple

theorem zero_closure_iff {H : NumericalSemigroup} (B : Base H) (x z : ℕ) :
    (x,0,z)∈SharedCap.Closure (SharedCap.ZeroGenerators (originals B)) ↔ B.N x z := by
  constructor
  · rintro ⟨g,⟨⟨e,he,rfl⟩,hey⟩,hle⟩
    refine ⟨e,⟨he,hey⟩,?_⟩
    intro i
    fin_cases i
    · simpa [tuple] using hle.1
    · simpa [tuple] using hle.2.1
    · simpa [tuple] using hle.2.2
  · rintro ⟨e,he,hle⟩
    refine ⟨tuple e,⟨⟨e,he.1,rfl⟩,he.2⟩,?_,?_,?_⟩
    · simpa [tuple] using hle 0
    · simpa [tuple] using hle 1
    · simpa [tuple] using hle 2

theorem nonfirst_wrap_original {H : NumericalSemigroup} (B : Base H) (D : Mode B)
    (G : Signature B D) (hgen : D.Genuine) (s : B.Source) (hnf : s≠B.first)
    (hy : 0<B.norm s 1) : B.N (B.norm s 0+B.u) (B.norm s 2+B.v) := by
  rcases normal_nonfirst_positive_y_shape B G.pure_b_live s hnf hy with h | h
  · exact B.N_upward (xy_strict_original B G.toRemainingGuards D hgen s hnf h.1 hy)
      le_rfl (by omega)
  · exact B.N_upward (yz_strict_original B G.toRemainingGuards D hgen s hnf hy h.2)
      (by omega) le_rfl

/-- The attained-cap data is OUTPUT of actual critical-return geometry.
The input contains genuine critical presentation and killed/live predecessors,
but no rectangle, source projection, cap-attainment, or compensation field. -/
def capData {H : NumericalSemigroup} (B : Base H) (D : Mode B)
    (G : Signature B D) (hgen : D.Genuine) : SharedCap.Data where
  C := B.C
  u := B.u
  v := B.v
  U := B.rightCap G.toRemainingGuards-B.u
  V := B.leftCap-B.v
  C_pos := B.critical.positive 1
  u_pos := B.u_pos
  v_pos := B.v_pos
  U_pos := by have := (B.cap_bounds G.toRemainingGuards).1; omega
  V_pos := by have := (B.cap_bounds G.toRemainingGuards).2.2.1; omega
  originals := originals B
  originals_finite := originals_finite B
  first := tuple (B.norm B.first)
  first_mem := ⟨B.norm B.first,Or.inl ⟨B.first,rfl⟩,rfl⟩
  first_y_pos := G.first_y_pos
  first_transverse_pos := by
    change 0<B.norm B.first 0+B.norm B.first 2
    have h := normal_not_pure_y B G.pure_b_live B.first
    omega
  normal := by
    rintro g ⟨e,he,rfl⟩
    rcases he with ⟨s,rfl⟩ | rfl
    · exact B.norm_y_lt s
    · simpa [tuple] using B.critical.positive 1
  shape := by
    rintro g ⟨e,he,rfl⟩ hnf hy
    rcases he with ⟨s,rfl⟩ | rfl
    · have hs : s≠B.first := fun h => hnf (congrArg (fun t => tuple (B.norm t)) h)
      rcases normal_nonfirst_positive_y_shape B G.pure_b_live s hs hy with h | h
      · exact Or.inl ⟨xy_projection_lower B G.toRemainingGuards D hgen s hs h.1 hy,h.2⟩
      · exact Or.inr ⟨yz_projection_lower B G.toRemainingGuards D hgen s hs hy h.2,h.1⟩
    · simp [tuple] at hy
  other_wraps := by
    rintro g ⟨e,he,rfl⟩ hnf hy
    rcases he with ⟨s,rfl⟩ | rfl
    · exact (zero_closure_iff B _ _).mpr (nonfirst_wrap_original B D G hgen s
        (fun h => hnf (congrArg (fun t => tuple (B.norm t)) h)) hy)
    · simp [tuple] at hy
  rectangle := by
    intro x z hx hz hmem
    have hb := B.cap_bounds G.toRemainingGuards
    exact B.rectangle G.toRemainingGuards (by omega) (by omega) ((zero_closure_iff B x z).mp hmem)
  central := by
    intro x z hx hz
    have hb := B.cap_bounds G.toRemainingGuards
    rw [zero_closure_iff]
    simpa only [Nat.add_sub_cancel' hb.1.le,Nat.add_sub_cancel' hb.2.2.1.le] using
      B.central_rectangle G.toRemainingGuards hx hz
  attained_x := by
    intro hfirstZ
    obtain ⟨s,hnf,hx,hy,hz⟩ := right_attained B D G hgen hfirstZ
    refine ⟨tuple (B.norm s),⟨B.norm s,Or.inl ⟨s,rfl⟩,rfl⟩,?_,hx,hy,hz⟩
    intro he
    have hh := congrArg (fun g : SharedCap.Monomial => g.2.2) he
    change B.norm s 2=B.norm B.first 2 at hh
    change 0<B.norm B.first 2 at hfirstZ
    omega
  attained_z := by
    intro hfirstX
    obtain ⟨s,hnf,hx,hy,hz⟩ := left_attained B D G hgen hfirstX
    refine ⟨tuple (B.norm s),⟨B.norm s,Or.inl ⟨s,rfl⟩,rfl⟩,?_,hx,hy,hz⟩
    intro he
    have hh := congrArg (fun g : SharedCap.Monomial => g.1) he
    change B.norm s 0=B.norm B.first 0 at hh
    change 0<B.norm B.first 0 at hfirstX
    omega

theorem remaining_compensation {H : NumericalSemigroup} (B : Base H) (D : Mode B)
    (G : Signature B D) (hgen : D.Genuine) :
    (capData B D G hgen).additionalWraps.ncard+(capData B D G hgen).fullSupport≤
      (capData B D G hgen).exceptional.ncard := SharedCap.compensation (capData B D G hgen)

end NS25Lean.GenericCriticalCompensation
