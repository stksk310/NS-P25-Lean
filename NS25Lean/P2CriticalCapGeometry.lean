import NS25Lean.P2CriticalShortFibers

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalCapGeometry
open Classical
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen
  ReturnSourceRigidity PureInternalTransverse CriticalNormalForm CriticalShortFibers

structure Base (H : NumericalSemigroup) where
  triple : Triple H
  critical : Critical triple
  m : ℕ
  m_pos : 0<m
  u : ℕ
  v : ℕ
  u_pos : 0<u
  v_pos : 0<v
  tie : critical.exponent 1*triple.g 1=u*triple.g 0+v*triple.g 2

abbrev Base.C {H : NumericalSemigroup} (B : Base H) := B.critical.exponent 1
abbrev Base.R {H : NumericalSemigroup} (B : Base H) := B.critical.exponent 0
abbrev Base.L {H : NumericalSemigroup} (B : Base H) := B.critical.exponent 2
abbrev Base.K {H : NumericalSemigroup} (B : Base H) := cyclicCut H B.m
abbrev Base.Source {H : NumericalSemigroup} (B : Base H) := IdealSources H B.K
def Base.norm {H : NumericalSemigroup} (B : Base H) (s : B.Source) : Exponent :=
  sourceNormal B.triple B.m B.C B.u B.v s
def Base.first {H : NumericalSemigroup} (B : Base H) : B.Source :=
  ⟨firstPrincipal H B.m B.m_pos*B.m,firstPrincipal_minimal_cut_source H B.m B.m_pos⟩
def Base.originals {H : NumericalSemigroup} (B : Base H) : Set Exponent :=
  Set.range B.norm∪{vector 0 0 B.L}
def Base.zeroOriginals {H : NumericalSemigroup} (B : Base H) : Set Exponent :=
  {g∈B.originals | g 1=0}
def Base.N {H : NumericalSemigroup} (B : Base H) (x z : ℕ) : Prop :=
  ∃ g∈B.zeroOriginals, g≤vector x 0 z

theorem Base.norm_degree {H : NumericalSemigroup} (B : Base H) (s : B.Source) :
    B.triple.weight (B.norm s)=s.val := sourceNormal_degree B.triple B.m B.C B.u B.v B.tie s
theorem Base.norm_y_lt {H : NumericalSemigroup} (B : Base H) (s : B.Source) :
    B.norm s 1<B.C := normal_y_lt B.C B.u B.v (B.critical.positive 1) _

theorem weight_cut_upward {H : NumericalSemigroup} (T : Triple H) (m : ℕ)
    {e f : Exponent} (he : T.weight e∈cyclicCut H m) (hle : e≤f) :
    T.weight f∈cyclicCut H m := by
  have hf : e+(f-e)=f := by
    ext i
    simp only [Finsupp.add_apply,Finsupp.tsub_apply]
    exact Nat.add_sub_of_le (hle i)
  have hh := ErasedSourceScreen.cut_add H he (T.member (f-e))
  rwa [←map_add,hf] at hh

theorem Base.N_upward {H : NumericalSemigroup} (B : Base H) {x z x' z' : ℕ}
    (h : B.N x z) (hx : x≤x') (hz : z≤z') : B.N x' z' := by
  obtain ⟨g,hg,he⟩ := h
  refine ⟨g,hg,le_trans he ?_⟩
  intro i
  fin_cases i <;> simp_all

theorem Base.original_cut {H : NumericalSemigroup} (B : Base H)
    (hboundary : B.L*B.triple.g 2∈B.K) {g : Exponent} (hg : g∈B.originals) :
    B.triple.weight g∈B.K := by
  rcases hg with ⟨s,rfl⟩ | rfl
  · rw [B.norm_degree]; exact s.property.1
  · simpa [vector_weight,Triple.grid] using hboundary

theorem Base.N_cut {H : NumericalSemigroup} (B : Base H)
    (hboundary : B.L*B.triple.g 2∈B.K) {x z : ℕ} (h : B.N x z) :
    B.triple.weight (vector x 0 z)∈B.K := by
  obtain ⟨g,hg,hle⟩ := h
  exact weight_cut_upward B.triple B.m (B.original_cut hboundary hg.1) hle

theorem Base.neck_out {H : NumericalSemigroup} (B : Base H)
    (hboundary : B.L*B.triple.g 2∈B.K)
    (hn : B.C*B.triple.g 1∉B.K) : ¬B.N B.u B.v := by
  intro h
  have hk := B.N_cut hboundary h
  have he : B.triple.weight (vector B.u 0 B.v)=B.C*B.triple.g 1 := by
    simpa [vector_weight,Triple.grid] using B.tie.symm
  exact hn (he ▸ hk)

theorem Base.zero_source_containing_neck_first {H : NumericalSemigroup} (B : Base H)
    (s : B.Source) (hx : B.u≤B.norm s 0) (hz : B.v≤B.norm s 2) : s=B.first := by
  have hp0 : 0<B.norm s 0 := lt_of_lt_of_le B.u_pos hx
  have hp2 : 0<B.norm s 2 := lt_of_lt_of_le B.v_pos hz
  have hs0 : B.triple.D s.val 0 := B.norm_degree s ▸ B.triple.D_of_coordinate _ 0 hp0
  have hs2 : B.triple.D s.val 2 := B.norm_degree s ▸ B.triple.D_of_coordinate _ 2 hp2
  let r := vector (B.norm s 0-B.u) (B.norm s 1+B.C) (B.norm s 2-B.v)
  have hr : B.triple.weight r=s.val := by
    have h0 := congrArg (fun n => n*B.triple.g 0) (Nat.sub_add_cancel hx)
    have h2 := congrArg (fun n => n*B.triple.g 2) (Nat.sub_add_cancel hz)
    have hs := B.norm_degree s
    rw [B.triple.weight_three,Triple.grid] at hs
    dsimp [r]
    rw [vector_weight,Triple.grid]
    nlinarith only [B.tie,h0,h2,hs]
  have hs1 : B.triple.D s.val 1 := hr ▸ B.triple.D_of_coordinate r 1
    (by simpa [r] using Nat.add_pos_right (B.norm s 1) (B.critical.positive 1))
  apply Subtype.ext
  apply full_support_source_is_first B.triple B.m B.m_pos s
  intro i
  fin_cases i <;> assumption

theorem Base.axis_source {H : NumericalSemigroup} (B : Base H)
    (hk : (B.R-1)*B.triple.g 0∈B.K) :
    ∃ s : B.Source, ∃ a : ℕ, 0<a ∧ a<B.R ∧ B.norm s=vector a 0 0 := by
  have hRpos : 0<B.R := B.critical.positive 0
  obtain ⟨s,hs⟩ := subcritical_axis_source_divisor B.triple B.critical B.m B.C B.u B.v
    B.tie 0 (B.R-1) (by change B.R-1<B.R; omega) hk
  change B.norm s≤Finsupp.single 0 (B.R-1) at hs
  have hx := hs 0
  have hy := hs 1
  have hz := hs 2
  simp only [Finsupp.single_eq_same,Finsupp.single_eq_of_ne (by decide : (1:Fin 3)≠0),
    Finsupp.single_eq_of_ne (by decide : (2:Fin 3)≠0)] at hx hy hz
  have hnY : B.norm s 1=0 := by omega
  have hnZ : B.norm s 2=0 := by omega
  have he : B.norm s=vector (B.norm s 0) 0 0 := by
    ext i
    fin_cases i <;> simp_all
  have hp : 0<B.norm s 0 := by
    by_contra hh
    have h0 : B.norm s 0=0 := by omega
    have hsdeg := B.norm_degree s
    rw [he,h0,vector_weight,Triple.grid] at hsdeg
    have hsrc := s.property.1
    obtain ⟨_,n,hn,r,_,hr⟩ := hsrc
    simp at hsdeg
    have hm := B.m_pos
    nlinarith
  exact ⟨s,B.norm s 0,hp,by omega,he⟩

structure RemainingGuards {H : NumericalSemigroup} (B : Base H) : Prop where
  axis_killed : (B.R-1)*B.triple.g 0∈B.K
  boundary_cut : B.L*B.triple.g 2∈B.K
  v_lt : B.v<B.L
  neck_uncut : B.C*B.triple.g 1∉B.K
  first_y_pos : 0<B.norm B.first 1

theorem Base.zero_original_arms {H : NumericalSemigroup} (B : Base H)
    (G : RemainingGuards B) {g : Exponent} (hg : g∈B.zeroOriginals) :
    (B.u<g 0 ∧ g 2<B.v) ∨ (g 0<B.u ∧ B.v<g 2) := by
  have hnotbelow : ¬(g 0≤B.u ∧ g 2≤B.v) := by
    rintro ⟨hx,hz⟩
    apply B.neck_out G.boundary_cut G.neck_uncut
    refine ⟨g,hg,?_⟩
    intro i
    fin_cases i
    · simpa using hx
    · simp [hg.2]
    · simpa using hz
  have hnotabove : ¬(B.u≤g 0 ∧ B.v≤g 2) := by
    rintro ⟨hx,hz⟩
    rcases hg.1 with ⟨s,rfl⟩ | h
    · have hs := B.zero_source_containing_neck_first s hx hz
      have hzero := hg.2
      rw [hs] at hzero
      have hy := G.first_y_pos
      omega
    · have he : g=vector 0 0 B.L := h
      have hu := B.u_pos
      simp [he] at hx
      omega
  omega

theorem Base.right_exists {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B) :
    ∃ x : ℕ, B.N x (B.v-1) := by
  obtain ⟨s,a,_,_,hs⟩ := B.axis_source G.axis_killed
  refine ⟨a,B.norm s,⟨Or.inl ⟨s,rfl⟩,by simp [hs]⟩,?_⟩
  rw [hs]
  intro i
  fin_cases i <;> simp

theorem Base.left_exists {H : NumericalSemigroup} (B : Base H) :
    ∃ z : ℕ, B.N (B.u-1) z := by
  refine ⟨B.L,vector 0 0 B.L,⟨Or.inr rfl,by simp⟩,?_⟩
  intro i
  fin_cases i <;> simp

def Base.rightCap {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B) : ℕ :=
  Nat.find (B.right_exists G)
def Base.leftCap {H : NumericalSemigroup} (B : Base H) : ℕ := Nat.find B.left_exists

theorem Base.rightCap_spec {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B) :
    B.N (B.rightCap G) (B.v-1) := Nat.find_spec (B.right_exists G)
theorem Base.leftCap_spec {H : NumericalSemigroup} (B : Base H) :
    B.N (B.u-1) B.leftCap := Nat.find_spec B.left_exists

theorem Base.rightCap_le {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B)
    {x z : ℕ} (hz : z<B.v) (h : B.N x z) : B.rightCap G≤x :=
  Nat.find_min' (B.right_exists G) (B.N_upward h le_rfl (by omega))
theorem Base.leftCap_le {H : NumericalSemigroup} (B : Base H)
    {x z : ℕ} (hx : x<B.u) (h : B.N x z) : B.leftCap≤z :=
  Nat.find_min' B.left_exists (B.N_upward h (by omega) le_rfl)

theorem Base.cap_bounds {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B) :
    B.u<B.rightCap G ∧ B.rightCap G<B.R ∧ B.v<B.leftCap ∧ B.leftCap≤B.L := by
  have hno := B.neck_out G.boundary_cut G.neck_uncut
  have hright : B.u<B.rightCap G := by
    by_contra hn
    exact hno (B.N_upward (B.rightCap_spec G) (by omega) (by omega))
  have hleft : B.v<B.leftCap := by
    by_contra hn
    exact hno (B.N_upward B.leftCap_spec (by omega) (by omega))
  obtain ⟨s,a,_,ha,hs⟩ := B.axis_source G.axis_killed
  have haxis : B.N a 0 := by
    refine ⟨B.norm s,⟨Or.inl ⟨s,rfl⟩,by simp [hs]⟩,?_⟩
    simp [hs]
  have hr := B.rightCap_le G B.v_pos haxis
  have hboundary : B.N (B.u-1) B.L := by
    refine ⟨vector 0 0 B.L,⟨Or.inr rfl,by simp⟩,?_⟩
    intro i
    fin_cases i <;> simp
  have hL := Nat.find_min' B.left_exists hboundary
  exact ⟨hright,lt_of_le_of_lt hr ha,hleft,hL⟩

theorem Base.rectangle {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B)
    {x z : ℕ} (hx : x<B.rightCap G) (hz : z<B.leftCap) : ¬B.N x z := by
  rintro ⟨g,hg,hle⟩
  have hgN : B.N (g 0) (g 2) := by
    refine ⟨g,hg,?_⟩
    intro i
    fin_cases i
    · simp
    · simp [hg.2]
    · simp
  have h0 : g 0≤x := by simpa using hle 0
  have h2 : g 2≤z := by simpa using hle 2
  rcases B.zero_original_arms G hg with h | h
  · have hh := B.rightCap_le G h.2 hgN
    omega
  · have hh := B.leftCap_le h.1 hgN
    omega

theorem Base.central_rectangle {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B)
    {x z : ℕ} (hx : B.u≤x) (hz : B.v≤z) :
    ¬B.N x z ↔ x<B.rightCap G ∧ z<B.leftCap := by
  constructor
  · intro hn
    constructor
    · by_contra hh
      exact hn (B.N_upward (B.rightCap_spec G) (by omega) (by omega))
    · by_contra hh
      exact hn (B.N_upward B.leftCap_spec (by omega) (by omega))
  · rintro ⟨h1,h2⟩
    exact B.rectangle G h1 h2

end NS25Lean.CriticalCapGeometry
