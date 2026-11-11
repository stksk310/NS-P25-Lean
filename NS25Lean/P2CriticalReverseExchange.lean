import NS25Lean.P2CriticalCapSources

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalReverseExchange
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen ReturnSourceRigidity
  PureInternalTransverse CriticalNormalForm CriticalShortFibers CriticalCapGeometry
  CriticalPresentationModes CriticalForwardExchange CriticalCapSources

def boundaryKilled {H : NumericalSemigroup} {B : Base H} : Mode B→Prop
  | .positive _ _ w z _ _ _ _ _ _ _ _ _ =>
      B.triple.weight (vector (w-1) z 0)∈B.K ∨ B.triple.weight (vector w (z-1) 0)∈B.K
  | .purePair _ => True

def inactiveKilled {H : NumericalSemigroup} {B : Base H} : Mode B→Prop
  | .positive p q _ _ _ _ _ _ _ _ _ _ _ =>
      B.triple.weight (vector 0 (p-1) q)∈B.K ∨ B.triple.weight (vector 0 p (q-1))∈B.K
  | .purePair _ => True

/-- Actual killed/live predecessor hypotheses. No cap, rectangle, or
transverse-source conclusion appears in this input signature. -/
structure Signature {H : NumericalSemigroup} (B : Base H) (D : Mode B) : Prop
    extends RemainingGuards B where
  pure_b_live : (B.C-1)*B.triple.g 1∉B.K
  pure_c_live : (B.L-1)*B.triple.g 2∉B.K
  boundary_killed : boundaryKilled D
  inactive_killed : inactiveKilled D

theorem divides_boundary_of_le {H : NumericalSemigroup} (B : Base H)
    (s : B.Source) (M : Exponent) (hdegree : B.triple.weight M=B.L*B.triple.g 2)
    (hle : B.norm s≤M) : ∃ d∈H, B.L*B.triple.g 2=s.val+d := by
  obtain ⟨d,hd,he⟩ := source_divides_monomial_degree B s M hle
  exact ⟨d,hd,hdegree ▸ he⟩

/-- A killed mixed-boundary predecessor below the genuine toric sides
extracts a pure-X source. RX excludes c, and source separation excludes a,b. -/
theorem killed_xy_boundary_axis {H : NumericalSemigroup} (B : Base H)
    (G : RemainingGuards B) (D : Mode B) (hgen : D.Genuine)
    (hlb : (B.C-1)*B.triple.g 1∉B.K) (hlc : (B.L-1)*B.triple.g 2∉B.K)
    (w z : ℕ) (hwR : w<B.R) (hzC : z<B.C)
    (hboundary : B.triple.weight (vector w z 0)=B.L*B.triple.g 2)
    (hcorner1 : D.xyCorner (w-1) z) (hcorner2 : D.xyCorner w (z-1))
    (hkill : B.triple.weight (vector (w-1) z 0)∈B.K ∨
      B.triple.weight (vector w (z-1) 0)∈B.K)
    (hfirstZ : 0<B.norm B.first 2) :
    ∃ s : B.Source, ∃ a : ℕ, 0<a ∧ a≤w ∧ B.norm s=vector a 0 0 := by
  obtain ⟨x,y,hx,hy,hcorner,hK⟩ : ∃ x y : ℕ, x≤w ∧ y≤z ∧
      D.xyCorner x y ∧ B.triple.weight (vector x y 0)∈B.K := by
    rcases hkill with h | h
    · exact ⟨w-1,z,by omega,le_rfl,hcorner1,h⟩
    · exact ⟨w,z-1,le_rfl,by omega,hcorner2,h⟩
  obtain ⟨s,hs,hxp,hsz⟩ := xy_source_of_short_cut B hlb x y
    (D.short_xy hgen x y (lt_of_le_of_lt hx hwR) (lt_of_le_of_lt hy hzC) hcorner) hK
  have hnf : s≠B.first := by
    intro h
    rw [h] at hsz
    omega
  have hdiv : ∃ d∈H, B.L*B.triple.g 2=s.val+d := by
    apply divides_boundary_of_le B s (vector w z 0) hboundary
    apply le_trans hs
    intro i
    fin_cases i <;> simp_all
  obtain ⟨n,k,hn,hkp,hkC,hret⟩ := axis_small_b_return B hlc s hnf hxp hdiv
  have hsy : B.norm s 1=0 := by
    by_contra h
    have hzero := coordinate_separation B s (B.norm s) (vector 0 k 0) (B.norm_degree s)
      n hn (by simpa only [vector_weight,Triple.grid,zero_mul,zero_add,add_zero] using hret)
      1 (by omega)
    simp at hzero
    omega
  refine ⟨s,B.norm s 0,hxp,?_,?_⟩
  · have hh := hs 0
    simp at hh
    omega
  · ext i
    fin_cases i <;> simp_all

theorem right_cap_divides_boundary {H : NumericalSemigroup} (B : Base H)
    (D : Mode B) (G : Signature B D) (hgen : D.Genuine)
    (hfirstZ : 0<B.norm B.first 2) (s : B.Source)
    (hs : B.norm s=vector (B.rightCap G.toRemainingGuards) 0 0) :
    ∃ d∈H, B.L*B.triple.g 2=s.val+d := by
  cases D with
  | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
    let D : Mode B := .positive p q w z hp hq hw hz hR hC hL hcenter hboundary
    have hk : B.triple.weight (vector (w-1) z 0)∈B.K ∨
        B.triple.weight (vector w (z-1) 0)∈B.K := G.boundary_killed
    have hdeg : B.triple.weight (vector w z 0)=B.L*B.triple.g 2 := by
      simpa only [vector_weight,Triple.grid,zero_mul,add_zero] using hboundary.symm
    obtain ⟨t,a,hap,haw,ht⟩ := killed_xy_boundary_axis B G.toRemainingGuards D hgen
      G.pure_b_live G.pure_c_live w z (by have := B.u_pos; omega) (by omega) hdeg
      (Or.inl (by omega)) (Or.inr (by omega)) hk hfirstZ
    have haN : B.N a 0 := by
      refine ⟨B.norm t,⟨Or.inl ⟨t,rfl⟩,by simp [ht]⟩,?_⟩
      simpa [ht] using (le_refl (vector a 0 0))
    have hcap := B.rightCap_le G.toRemainingGuards B.v_pos haN
    apply divides_boundary_of_le B s (vector w z 0) hdeg
    rw [hs]
    intro i
    fin_cases i <;> simp_all <;> omega
  | purePair hpair =>
    have hb := B.cap_bounds G.toRemainingGuards
    apply divides_boundary_of_le B s (vector B.R 0 0)
      (by simpa only [vector_weight,Triple.grid,zero_mul,zero_add,add_zero] using hpair)
    rw [hs]
    intro i
    fin_cases i <;> simp_all <;> omega

end NS25Lean.CriticalReverseExchange
