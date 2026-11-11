import NS25Lean.P2CriticalPresentationModes

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalForwardExchange
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen ReturnSourceRigidity
  PureInternalTransverse CriticalNormalForm CriticalShortFibers CriticalCapGeometry CriticalPresentationModes

theorem coordinate_separation {H : NumericalSemigroup} (B : Base H) (s : B.Source)
    (g t : Exponent) (hg : B.triple.weight g=s.val) (n : ℕ) (hn : 0<n)
    (hret : s.val=n*B.m+B.triple.weight t) (i : Fin 3) (hi : 0<g i) : t i=0 := by
  let se : Sources H B.m Set.univ := ⟨s.val,by simpa only [returnCut_univ] using s.property⟩
  by_contra ht
  exact source_remainder_support_disjoint B.triple B.m Set.univ se (Set.mem_univ n) hn hret
    (hg ▸ B.triple.D_of_coordinate g i hi) (B.triple.D_of_coordinate t i (by omega))

theorem normal_not_pure_y {H : NumericalSemigroup} (B : Base H)
    (hlive : (B.C-1)*B.triple.g 1∉B.K) (s : B.Source) :
    ¬(B.norm s 0=0 ∧ B.norm s 2=0) := by
  rintro ⟨hx,hz⟩
  have he := B.norm_degree s
  simp only [B.triple.weight_three,Triple.grid,hx,hz,zero_mul,zero_add,add_zero] at he
  have hcut : B.norm s 1*B.triple.g 1∈B.K := he.symm ▸ s.property.1
  exact below_live_not_cut B.critical B.m 1 hlive (B.norm_y_lt s) hcut

theorem normal_nonfirst_positive_y_shape {H : NumericalSemigroup} (B : Base H)
    (hlive : (B.C-1)*B.triple.g 1∉B.K) (s : B.Source) (hs : s≠B.first)
    (hy : 0<B.norm s 1) :
    (0<B.norm s 0 ∧ B.norm s 2=0) ∨ (B.norm s 0=0 ∧ 0<B.norm s 2) := by
  have hnot := normal_not_pure_y B hlive s
  by_cases hx : 0<B.norm s 0
  · left
    refine ⟨hx,?_⟩
    by_contra hn
    have hz : 0<B.norm s 2 := by omega
    have hfull : FullSupport B.triple s.val := by
      intro i
      rw [←B.norm_degree s]
      apply B.triple.D_of_coordinate
      fin_cases i <;> assumption
    exact hs (Subtype.ext (full_support_source_is_first B.triple B.m B.m_pos s hfull))
  · exact Or.inr ⟨by omega,by omega⟩

theorem zero_cut_in_N_of_unique {H : NumericalSemigroup} (B : Base H)
    (x z : ℕ) (hUF : ∀ e, B.triple.weight e=B.triple.weight (vector x 0 z) → e=vector x 0 z)
    (hcut : B.triple.weight (vector x 0 z)∈B.K) : B.N x z := by
  obtain ⟨s,hs⟩ := cut_normal_source_divisor_of_unique B.triple B.m B.C B.u B.v B.tie
    (vector x 0 z) hUF hcut
  change B.norm s≤vector x 0 z at hs
  have hy : B.norm s 1=0 := by have hh := hs 1; simpa using Nat.le_zero.mp (by simpa using hh)
  exact ⟨B.norm s,⟨Or.inl ⟨s,rfl⟩,hy⟩,hs⟩

/-- RE2 yields a strict ORIGINAL predecessor of the nonfirst XY wrap. -/
theorem xy_strict_original_core {H : NumericalSemigroup} (B : Base H)
    (haxisKilled : (B.R-1)*B.triple.g 0∈B.K) (hvLt : B.v<B.L)
    (D : Mode B) (hgen : D.Genuine) (s : B.Source) (hs : s≠B.first)
    (hx : 0<B.norm s 0) (hy : 0<B.norm s 1) : B.N (B.norm s 0+B.u) (B.v-1) := by
  have hz : B.norm s 2=0 := by
    by_contra hh
    have hfull : FullSupport B.triple s.val := by
      intro i
      fin_cases i
      · exact B.norm_degree s ▸ B.triple.D_of_coordinate (B.norm s) 0 hx
      · exact B.norm_degree s ▸ B.triple.D_of_coordinate (B.norm s) 1 hy
      · exact B.norm_degree s ▸ B.triple.D_of_coordinate (B.norm s) 2 (Nat.pos_of_ne_zero hh)
    exact hs (Subtype.ext (full_support_source_is_first B.triple B.m B.m_pos s hfull))
  obtain ⟨n,r,hn,_,hr,hrpos,hret⟩ := nonfirst_source_small_return H B.m B.m_pos s
    (fun h => hs (Subtype.ext h))
  obtain ⟨t,ht⟩ := B.triple.factor r hr
  have hret' : s.val=n*B.m+B.triple.weight t := by omega
  have ht0 := coordinate_separation B s (B.norm s) t (B.norm_degree s) n hn hret' 0 hx
  have ht1 := coordinate_separation B s (B.norm s) t (B.norm_degree s) n hn hret' 1 hy
  have ht2 : 0<t 2 := by
    have hw := B.triple.weight_three t
    dsimp [Triple.grid] at hw
    simp only [ht0,ht1,zero_mul,zero_add] at hw
    nlinarith only [hw,ht,hrpos]
  have htEq : t=vector 0 0 (t 2) := by
    ext i
    fin_cases i <;> simp_all
  let M := vector (B.norm s 0+B.u) 0 (B.v-1)
  have hcut : B.triple.weight M∈B.K := by
    apply critical_transport_cut B.triple B.m n B.C B.u B.v hn B.tie (B.norm s)
      t M (vector 0 (B.C-B.norm s 1) (t 2-1)) (-1)
    · rw [B.norm_degree]; exact hret'
    · simp [M,ht0] <;> omega
    · have hb := B.norm_y_lt s
      simp [M,ht1] <;> omega
    · have hv := B.v_pos
      simp [M,hz] <;> omega
  obtain ⟨a,hap,haR,ha⟩ : ∃ a : ℕ, 0<a ∧ a<B.R ∧ B.N a 0 := by
    obtain ⟨v,a,hap,haR,hv⟩ := B.axis_source haxisKilled
    refine ⟨a,hap,haR,B.norm v,⟨Or.inl ⟨v,rfl⟩,by simp [hv]⟩,?_⟩
    simpa [hv] using (le_refl (vector a 0 0))
  by_cases haxis : a≤B.norm s 0+B.u
  · exact B.N_upward ha haxis (Nat.zero_le _)
  · apply zero_cut_in_N_of_unique B _ _ _ hcut
    exact D.short_xz hgen _ _ (by omega) (by omega)
      (Or.inr (by have := B.v_pos; omega))

theorem xy_strict_original {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B)
    (D : Mode B) (hgen : D.Genuine) (s : B.Source) (hs : s≠B.first)
    (hx : 0<B.norm s 0) (hy : 0<B.norm s 1) : B.N (B.norm s 0+B.u) (B.v-1) :=
  xy_strict_original_core B G.axis_killed G.v_lt D hgen s hs hx hy

/-- RE3 is the exact transpose and retains the boundary cap D=L. -/
theorem yz_strict_original_core {H : NumericalSemigroup} (B : Base H) (huLt : B.u<B.R)
    (D : Mode B) (hgen : D.Genuine) (s : B.Source) (hs : s≠B.first)
    (hy : 0<B.norm s 1) (hz : 0<B.norm s 2) : B.N (B.u-1) (B.norm s 2+B.v) := by
  have hx : B.norm s 0=0 := by
    by_contra hh
    have hfull : FullSupport B.triple s.val := by
      intro i
      fin_cases i
      · exact B.norm_degree s ▸ B.triple.D_of_coordinate (B.norm s) 0 (Nat.pos_of_ne_zero hh)
      · exact B.norm_degree s ▸ B.triple.D_of_coordinate (B.norm s) 1 hy
      · exact B.norm_degree s ▸ B.triple.D_of_coordinate (B.norm s) 2 hz
    exact hs (Subtype.ext (full_support_source_is_first B.triple B.m B.m_pos s hfull))
  obtain ⟨n,r,hn,_,hr,hrpos,hret⟩ := nonfirst_source_small_return H B.m B.m_pos s
    (fun h => hs (Subtype.ext h))
  obtain ⟨t,ht⟩ := B.triple.factor r hr
  have hret' : s.val=n*B.m+B.triple.weight t := by omega
  have ht1 := coordinate_separation B s (B.norm s) t (B.norm_degree s) n hn hret' 1 hy
  have ht2 := coordinate_separation B s (B.norm s) t (B.norm_degree s) n hn hret' 2 hz
  have ht0 : 0<t 0 := by
    have hw := B.triple.weight_three t
    dsimp [Triple.grid] at hw
    simp only [ht1,ht2,zero_mul,add_zero] at hw
    nlinarith only [hw,ht,hrpos]
  let M := vector (B.u-1) 0 (B.norm s 2+B.v)
  have hcut : B.triple.weight M∈B.K := by
    apply critical_transport_cut B.triple B.m n B.C B.u B.v hn B.tie (B.norm s)
      t M (vector (t 0-1) (B.C-B.norm s 1) 0) (-1)
    · rw [B.norm_degree]; exact hret'
    · have hu := B.u_pos
      simp [M,hx] <;> omega
    · have hb := B.norm_y_lt s
      simp [M,ht1] <;> omega
    · simp [M,ht2] <;> omega
  by_cases haxis : B.L≤B.norm s 2+B.v
  · refine ⟨vector 0 0 B.L,⟨Or.inr rfl,by simp⟩,?_⟩
    intro i
    fin_cases i <;> simp_all
  · apply zero_cut_in_N_of_unique B _ _ _ hcut
    exact D.short_xz hgen _ _ (by omega) (by omega)
      (Or.inl (by have := B.u_pos; omega))

theorem yz_strict_original {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B)
    (D : Mode B) (hgen : D.Genuine) (s : B.Source) (hs : s≠B.first)
    (hy : 0<B.norm s 1) (hz : 0<B.norm s 2) : B.N (B.u-1) (B.norm s 2+B.v) := by
  have hb := B.cap_bounds G
  exact yz_strict_original_core B (lt_trans hb.1 hb.2.1) D hgen s hs hy hz

theorem xy_projection_lower {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B)
    (D : Mode B) (hgen : D.Genuine) (s : B.Source) (hs : s≠B.first)
    (hx : 0<B.norm s 0) (hy : 0<B.norm s 1) : B.rightCap G-B.u≤B.norm s 0 := by
  have hh := B.rightCap_le G (by have := B.v_pos; omega)
    (xy_strict_original B G D hgen s hs hx hy)
  omega

theorem yz_projection_lower {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B)
    (D : Mode B) (hgen : D.Genuine) (s : B.Source) (hs : s≠B.first)
    (hy : 0<B.norm s 1) (hz : 0<B.norm s 2) : B.leftCap-B.v≤B.norm s 2 := by
  have hh := B.leftCap_le (by have := B.u_pos; omega)
    (yz_strict_original B G D hgen s hs hy hz)
  omega

end NS25Lean.CriticalForwardExchange
