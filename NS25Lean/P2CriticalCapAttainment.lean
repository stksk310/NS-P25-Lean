import NS25Lean.P2CriticalReverseExchange

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalCapAttainment
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen ReturnSourceRigidity
  PureInternalTransverse CriticalNormalForm CriticalShortFibers CriticalCapGeometry
  CriticalPresentationModes CriticalForwardExchange CriticalCapSources CriticalReverseExchange

theorem right_forcing_of_return {H : NumericalSemigroup} (B : Base H) (D : Mode B)
    (G : Signature B D) (hgen : D.Genuine) (hfirstZ : 0<B.norm B.first 2)
    (s : B.Source) (e n k : ℕ) (hs : B.norm s=vector (B.rightCap G.toRemainingGuards) 0 e)
    (he : e<B.v) (hn : 0<n) (hk : 0<k) (hkC : k<B.C)
    (hret : s.val=n*B.m+k*B.triple.g 1) :
    ∃ t : B.Source, t≠B.first ∧ B.norm t 0=B.rightCap G.toRemainingGuards-B.u ∧
      0<B.norm t 1 ∧ B.norm t 2=0 := by
  have hb := B.cap_bounds G.toRemainingGuards
  let M := vector (B.rightCap G.toRemainingGuards-B.u) (B.C-k) 0
  have hcut : B.triple.weight M∈B.K := by
    apply critical_transport_cut B.triple B.m n B.C B.u B.v hn B.tie (B.norm s)
      (vector 0 k 0) M (vector 0 0 (B.v-e)) 1
    · rw [B.norm_degree]
      simpa only [vector_weight,Triple.grid,zero_mul,zero_add,add_zero] using hret
    · simp [M,hs]; omega
    · simp [M,hs]; omega
    · simp [M,hs]; omega
  have hcorner : D.xyCorner (B.rightCap G.toRemainingGuards-B.u) (B.C-k) := by
    cases D with
    | positive p q w z hp hq hw hz hR hC hL hcenter hboundary => exact Or.inl (by omega)
    | purePair hpair => trivial
  obtain ⟨t,ht,htx,htz⟩ := xy_source_of_short_cut B G.pure_b_live _ _
    (D.short_xy hgen _ _ (by omega) (by omega) hcorner) hcut
  have ht0 : B.norm t 0≤B.rightCap G.toRemainingGuards-B.u := by simpa [M] using ht 0
  have hty : 0<B.norm t 1 := by
    by_contra hh
    have hy0 : B.norm t 1=0 := by omega
    have hN : B.N (B.norm t 0) 0 := by
      refine ⟨B.norm t,⟨Or.inl ⟨t,rfl⟩,hy0⟩,?_⟩
      intro i
      fin_cases i <;> simp_all
    have hmin := B.rightCap_le G.toRemainingGuards B.v_pos hN
    have hu := B.u_pos
    omega
  have hnf : t≠B.first := by intro hh; rw [hh] at htz; omega
  have hlo := xy_projection_lower B G.toRemainingGuards D hgen t hnf htx hty
  exact ⟨t,hnf,Nat.le_antisymm ht0 hlo,hty,htz⟩

theorem right_attained {H : NumericalSemigroup} (B : Base H) (D : Mode B)
    (G : Signature B D) (hgen : D.Genuine) (hfirstZ : 0<B.norm B.first 2) :
    ∃ t : B.Source, t≠B.first ∧ B.norm t 0=B.rightCap G.toRemainingGuards-B.u ∧
      0<B.norm t 1 ∧ B.norm t 2=0 := by
  obtain ⟨s,e,he,hs⟩ := right_cap_source B G.toRemainingGuards
  have hb := B.cap_bounds G.toRemainingGuards
  have hnf : s≠B.first := by
    intro hh
    have hy0 := congrArg (fun g : Exponent => g 1) hs
    rw [hh] at hy0
    simp at hy0
    have hy := G.first_y_pos
    omega
  have hx : 0<B.norm s 0 := by simp [hs]; have := B.u_pos; omega
  by_cases he0 : e=0
  · have hs0 : B.norm s=vector (B.rightCap G.toRemainingGuards) 0 0 := by simpa [he0] using hs
    have hdiv := right_cap_divides_boundary B D G hgen hfirstZ s hs0
    obtain ⟨n,k,hn,hk,hkC,hret⟩ := axis_small_b_return B G.pure_c_live s hnf hx hdiv
    exact right_forcing_of_return B D G hgen hfirstZ s e n k hs he hn hk hkC hret
  · obtain ⟨n,k,hn,hk,hkC,hret⟩ := xz_small_b_return B s hnf hx (by simp [hs]; omega)
    exact right_forcing_of_return B D G hgen hfirstZ s e n k hs he hn hk hkC hret

theorem yz_mixed_source_of_cut {H : NumericalSemigroup} (B : Base H) (D : Mode B)
    (G : Signature B D) (hgen : D.Genuine) (hfirstX : 0<B.norm B.first 0)
    (y z : ℕ) (hy : y<B.C) (hz : z<B.L) (hcorner : D.yzCorner y z)
    (hcut : B.triple.weight (vector 0 y z)∈B.K) :
    ∃ t : B.Source, B.norm t≤vector 0 y z ∧ t≠B.first ∧
      B.norm t 0=0 ∧ 0<B.norm t 1 ∧ 0<B.norm t 2 := by
  obtain ⟨t,ht,htx,htz⟩ := yz_source_of_short_cut B G.pure_b_live y z
    (D.short_yz hgen y z hy hz hcorner) hcut
  have hty : 0<B.norm t 1 := by
    by_contra hh
    have hy0 : B.norm t 1=0 := by omega
    have he := B.norm_degree t
    simp only [B.triple.weight_three,Triple.grid,htx,hy0,zero_mul,zero_add] at he
    have hK : B.norm t 2*B.triple.g 2∈B.K := he.symm ▸ t.property.1
    have hlt : B.norm t 2<B.L := by have hh' := ht 2; simp at hh'; omega
    exact below_live_not_cut B.critical B.m 2 G.pure_c_live hlt hK
  have hnf : t≠B.first := by intro hh; rw [hh] at htx; omega
  exact ⟨t,ht,hnf,htx,hty,htz⟩

theorem left_attained_of_cut {H : NumericalSemigroup} (B : Base H) (D : Mode B)
    (G : Signature B D) (hgen : D.Genuine) (hfirstX : 0<B.norm B.first 0)
    (y : ℕ) (hy : y<B.C) (hcorner : D.yzCorner y (B.leftCap-B.v))
    (hcut : B.triple.weight (vector 0 y (B.leftCap-B.v))∈B.K) :
    ∃ t : B.Source, t≠B.first ∧ B.norm t 0=0 ∧
      0<B.norm t 1 ∧ B.norm t 2=B.leftCap-B.v := by
  have hb := B.cap_bounds G.toRemainingGuards
  obtain ⟨t,ht,hnf,htx,hty,htz⟩ := yz_mixed_source_of_cut B D G hgen hfirstX y
    (B.leftCap-B.v) hy (by have := B.v_pos; omega) hcorner hcut
  have hlo := yz_projection_lower B G.toRemainingGuards D hgen t hnf hty htz
  have hup : B.norm t 2≤B.leftCap-B.v := by simpa using ht 2
  exact ⟨t,hnf,htx,hty,Nat.le_antisymm hup hlo⟩

theorem left_strict_attained {H : NumericalSemigroup} (B : Base H) (D : Mode B)
    (G : Signature B D) (hgen : D.Genuine) (hfirstX : 0<B.norm B.first 0)
    (hstrict : B.leftCap<B.L) :
    ∃ t : B.Source, t≠B.first ∧ B.norm t 0=0 ∧
      0<B.norm t 1 ∧ B.norm t 2=B.leftCap-B.v := by
  obtain hboundary | ⟨s,d,hd,hs⟩ := left_cap_source_or_boundary B G.toRemainingGuards
  · omega
  have hb := B.cap_bounds G.toRemainingGuards
  have hnf : s≠B.first := by
    intro hh
    have hy0 := congrArg (fun g : Exponent => g 1) hs
    rw [hh] at hy0
    simp at hy0
    have hy := G.first_y_pos
    omega
  have hdp : 0<d := by
    by_contra hh
    have hd0 : d=0 := by omega
    have he := B.norm_degree s
    rw [hs,hd0,vector_weight] at he
    simp only [Triple.grid,zero_mul,zero_add] at he
    exact below_live_not_cut B.critical B.m 2 G.pure_c_live hstrict (he.symm ▸ s.property.1)
  obtain ⟨n,k,hn,hk,hkC,hret⟩ := xz_small_b_return B s hnf (by simpa [hs] using hdp)
    (by simp [hs]; have := B.v_pos; omega)
  let M := vector 0 (B.C-k) (B.leftCap-B.v)
  have hcut : B.triple.weight M∈B.K := by
    apply critical_transport_cut B.triple B.m n B.C B.u B.v hn B.tie (B.norm s)
      (vector 0 k 0) M (vector (B.u-d) 0 0) 1
    · rw [B.norm_degree]
      simpa only [vector_weight,Triple.grid,zero_mul,zero_add,add_zero] using hret
    · simp [M,hs]; omega
    · simp [M,hs]; omega
    · simp [M,hs]; omega
  apply left_attained_of_cut B D G hgen hfirstX (B.C-k) (by omega) _ hcut
  cases D with
  | positive p q w z hp hq hw hz hR hC hL hcenter hboundary => exact Or.inr (by omega)
  | purePair hpair => trivial

/-- The inclusive endpoint D=L is retained. In the positive presentation it
uses the killed inactive mixed predecessor; in the pure-pair presentation
RE6 is an actual positive return followed by the single F transport. -/
theorem left_equality_attained {H : NumericalSemigroup} (B : Base H) (D : Mode B)
    (G : Signature B D) (hgen : D.Genuine) (hfirstX : 0<B.norm B.first 0)
    (heq : B.leftCap=B.L) :
    ∃ t : B.Source, t≠B.first ∧ B.norm t 0=0 ∧
      0<B.norm t 1 ∧ B.norm t 2=B.leftCap-B.v := by
  have hb := B.cap_bounds G.toRemainingGuards
  cases D with
  | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
    let D : Mode B := .positive p q w z hp hq hw hz hR hC hL hcenter hboundary
    have hqeq : B.leftCap-B.v=q := by omega
    have hk : B.triple.weight (vector 0 (p-1) q)∈B.K ∨
        B.triple.weight (vector 0 p (q-1))∈B.K := G.inactive_killed
    rcases hk with hk | hk
    · apply left_attained_of_cut B D G hgen hfirstX (p-1) (by omega)
        (Or.inl (by omega))
      simpa only [hqeq] using hk
    · obtain ⟨t,ht,hnf,htx,hty,htz⟩ := yz_mixed_source_of_cut B D G hgen hfirstX p (q-1)
        (by omega) (by have := B.v_pos; omega) (Or.inr (by omega)) hk
      have hlo := yz_projection_lower B G.toRemainingGuards D hgen t hnf hty htz
      have hup : B.norm t 2≤q-1 := by simpa using ht 2
      rw [hqeq] at hlo
      omega
  | purePair hpair =>
    let D : Mode B := .purePair hpair
    obtain ⟨s,a,hap,haR,hs⟩ := B.axis_source G.axis_killed
    have hnf : s≠B.first := by
      intro hh
      have hy0 := congrArg (fun g : Exponent => g 1) hs
      rw [hh] at hy0
      simp at hy0
      have hy := G.first_y_pos
      omega
    have hdiv : ∃ d∈H, B.L*B.triple.g 2=s.val+d := by
      apply divides_boundary_of_le B s (vector B.R 0 0)
        (by simpa only [vector_weight,Triple.grid,zero_mul,zero_add,add_zero] using hpair)
      rw [hs]
      intro i
      fin_cases i <;> simp_all <;> omega
    obtain ⟨n,k,hn,hkp,hkC,hret⟩ := axis_small_b_return B G.pure_c_live s hnf
      (by simpa [hs] using hap) hdiv
    have hsource : a*B.triple.g 0=s.val := by
      have hh := B.norm_degree s
      simpa only [hs,vector_weight,Triple.grid,zero_mul,zero_add,add_zero] using hh
    have hbase : B.triple.weight (vector 0 0 B.L)=
        n*B.m+B.triple.weight (vector (B.R-a) k 0) := by
      have hsplit := congrArg (fun t => t*B.triple.g 0) (Nat.sub_add_cancel haR.le)
      simp only [Nat.add_mul] at hsplit
      simp only [vector_weight,Triple.grid,zero_mul,zero_add,add_zero]
      nlinarith only [hpair,hsource,hret,hsplit]
    let M := vector 0 (B.C-k) (B.L-B.v)
    have hcut : B.triple.weight M∈B.K := by
      apply critical_transport_cut B.triple B.m n B.C B.u B.v hn B.tie
        (vector 0 0 B.L) (vector (B.R-a) k 0) M (vector (B.R+B.u-a) 0 0) 1 hbase
      · simp [M]; omega
      · simp [M]; omega
      · have hv := G.v_lt
        simp [M]; omega
    apply left_attained_of_cut B D G hgen hfirstX (B.C-k) (by omega) trivial
    simpa only [heq] using hcut

theorem left_attained {H : NumericalSemigroup} (B : Base H) (D : Mode B)
    (G : Signature B D) (hgen : D.Genuine) (hfirstX : 0<B.norm B.first 0) :
    ∃ t : B.Source, t≠B.first ∧ B.norm t 0=0 ∧
      0<B.norm t 1 ∧ B.norm t 2=B.leftCap-B.v := by
  by_cases h : B.leftCap=B.L
  · exact left_equality_attained B D G hgen hfirstX h
  · have hb := B.cap_bounds G.toRemainingGuards
    exact left_strict_attained B D G hgen hfirstX (by omega)

end NS25Lean.CriticalCapAttainment
