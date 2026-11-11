import NS25Lean.P2CriticalForwardExchange

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalCapSources
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen ReturnSourceRigidity
  PureInternalTransverse CriticalNormalForm CriticalShortFibers CriticalCapGeometry
  CriticalPresentationModes CriticalForwardExchange

theorem right_cap_source {H : NumericalSemigroup} (B : Base H) (G : RemainingGuards B) :
    ∃ s : B.Source, ∃ e : ℕ, e<B.v ∧ B.norm s=vector (B.rightCap G) 0 e := by
  obtain ⟨g,hg,hle⟩ := B.rightCap_spec G
  have hx : g 0≤B.rightCap G := by simpa using hle 0
  have hz : g 2<B.v := by have hh := hle 2; simp at hh; have := B.v_pos; omega
  have hgN : B.N (g 0) (g 2) := by
    refine ⟨g,hg,?_⟩
    intro i
    fin_cases i <;> simp [hg.2]
  have hxeq : g 0=B.rightCap G := Nat.le_antisymm hx (B.rightCap_le G hz hgN)
  rcases hg.1 with ⟨s,rfl⟩ | hg'
  · refine ⟨s,B.norm s 2,hz,?_⟩
    ext i
    fin_cases i
    · simpa using hxeq
    · simpa using hg.2
    · simp
  · have he : g=vector 0 0 B.L := hg'
    have hv := G.v_lt
    simp [he] at hz
    omega

theorem left_cap_source_or_boundary {H : NumericalSemigroup} (B : Base H)
    (G : RemainingGuards B) : B.leftCap=B.L ∨
      ∃ s : B.Source, ∃ d : ℕ, d<B.u ∧ B.norm s=vector d 0 B.leftCap := by
  obtain ⟨g,hg,hle⟩ := B.leftCap_spec
  have hx : g 0<B.u := by have hh := hle 0; simp at hh; have := B.u_pos; omega
  have hz : g 2≤B.leftCap := by simpa using hle 2
  have hgN : B.N (g 0) (g 2) := by
    refine ⟨g,hg,?_⟩
    intro i
    fin_cases i <;> simp [hg.2]
  have hzeq : g 2=B.leftCap := Nat.le_antisymm hz (B.leftCap_le hx hgN)
  rcases hg.1 with ⟨s,rfl⟩ | hg'
  · right
    refine ⟨s,B.norm s 0,hx,?_⟩
    ext i
    fin_cases i
    · simp
    · simpa using hg.2
    · simpa using hzeq
  · have he : g=vector 0 0 B.L := hg'
    simp [he] at hzeq
    exact Or.inl hzeq.symm

theorem source_divides_monomial_degree {H : NumericalSemigroup} (B : Base H)
    (s : B.Source) (M : Exponent) (hle : B.norm s≤M) :
    ∃ d∈H, B.triple.weight M=s.val+d := by
  have he : B.norm s+(M-B.norm s)=M := by
    ext i
    simp only [Finsupp.add_apply,Finsupp.tsub_apply]
    exact Nat.add_sub_of_le (hle i)
  refine ⟨B.triple.weight (M-B.norm s),B.triple.member _,?_⟩
  have hw := congrArg B.triple.weight he
  rw [map_add,B.norm_degree] at hw
  exact hw.symm

/-- RX at the ACTUAL pure-c predecessor, with H membership retained. -/
theorem boundary_reflection_excludes_c {H : NumericalSemigroup} (B : Base H)
    (hlive : (B.L-1)*B.triple.g 2∉B.K) (s : B.Source)
    (hdiv : ∃ d∈H, B.L*B.triple.g 2=s.val+d)
    (n r : ℕ) (hn : 0<n) (hret : s.val=n*B.m+r) : ¬B.triple.D r 2 := by
  rintro ⟨e,he,her⟩
  obtain ⟨d,hd,hdiv⟩ := hdiv
  have hpred := B.triple.member (Finsupp.single 2 (B.L-1))
  rw [B.triple.weight_single] at hpred
  have hLpos : 0<B.L := B.critical.positive 2
  have hhg : B.L*B.triple.g 2=B.triple.g 2+(B.L-1)*B.triple.g 2 := by
    have h := congrArg (fun t => t*B.triple.g 2) (show B.L-1+1=B.L by omega)
    simp only [Nat.add_mul,one_mul] at h
    omega
  exact hlive (guarded_live_reflection H B.m n s.val r (B.L*B.triple.g 2)
    (B.triple.g 2) d e ((B.L-1)*B.triple.g 2) hn hret hd he hpred hdiv
      (by omega) hhg)

theorem b_return_exponent_lt {H : NumericalSemigroup} (B : Base H) (s : B.Source)
    (hx : 0<B.norm s 0) (n k : ℕ) (hn : 0<n)
    (hret : s.val=n*B.m+k*B.triple.g 1) : k<B.C := by
  by_contra hh
  have hle : B.C≤k := by omega
  let t := vector B.u (k-B.C) B.v
  have ht : B.triple.weight t=k*B.triple.g 1 := by
    have h := congrArg (fun t => t*B.triple.g 1) (Nat.sub_add_cancel hle)
    simp only [Nat.add_mul] at h
    dsimp [t]
    rw [vector_weight,Triple.grid]
    nlinarith only [B.tie,h]
  have hzero := coordinate_separation B s (B.norm s) t (B.norm_degree s) n hn
    (hret.trans (by rw [ht])) 0 hx
  have hu := B.u_pos
  simp [t] at hzero
  omega

theorem xz_small_b_return {H : NumericalSemigroup} (B : Base H)
    (s : B.Source) (hs : s≠B.first) (hx : 0<B.norm s 0) (hz : 0<B.norm s 2) :
    ∃ n k : ℕ, 0<n ∧ 0<k ∧ k<B.C ∧ s.val=n*B.m+k*B.triple.g 1 := by
  obtain ⟨n,r,hn,_,hr,hp,hret⟩ := nonfirst_source_small_return H B.m B.m_pos s
    (fun h => hs (Subtype.ext h))
  obtain ⟨t,ht⟩ := B.triple.factor r hr
  have hret' : s.val=n*B.m+B.triple.weight t := by omega
  have h0 := coordinate_separation B s (B.norm s) t (B.norm_degree s) n hn hret' 0 hx
  have h2 := coordinate_separation B s (B.norm s) t (B.norm_degree s) n hn hret' 2 hz
  have hrb : r=t 1*B.triple.g 1 := by
    simpa only [B.triple.weight_three,Triple.grid,h0,h2,zero_mul,zero_add,add_zero] using ht.symm
  have hkp : 0<t 1 := by nlinarith
  have he : s.val=n*B.m+t 1*B.triple.g 1 := by omega
  exact ⟨n,t 1,hn,hkp,b_return_exponent_lt B s hx n (t 1) hn he,he⟩

theorem axis_small_b_return {H : NumericalSemigroup} (B : Base H)
    (hlive : (B.L-1)*B.triple.g 2∉B.K) (s : B.Source) (hs : s≠B.first)
    (hx : 0<B.norm s 0)
    (hdiv : ∃ d∈H, B.L*B.triple.g 2=s.val+d) :
    ∃ n k : ℕ, 0<n ∧ 0<k ∧ k<B.C ∧ s.val=n*B.m+k*B.triple.g 1 := by
  obtain ⟨n,r,hn,_,hr,hp,hret⟩ := nonfirst_source_small_return H B.m B.m_pos s
    (fun h => hs (Subtype.ext h))
  obtain ⟨t,ht⟩ := B.triple.factor r hr
  have hret' : s.val=n*B.m+B.triple.weight t := by omega
  have h0 := coordinate_separation B s (B.norm s) t (B.norm_degree s) n hn hret' 0 hx
  have h2 : t 2=0 := by
    by_contra h
    exact boundary_reflection_excludes_c B hlive s hdiv n r hn hret
      (ht ▸ B.triple.D_of_coordinate t 2 (by omega))
  have hrb : r=t 1*B.triple.g 1 := by
    simpa only [B.triple.weight_three,Triple.grid,h0,h2,zero_mul,zero_add,add_zero] using ht.symm
  have hkp : 0<t 1 := by nlinarith
  have he : s.val=n*B.m+t 1*B.triple.g 1 := by omega
  exact ⟨n,t 1,hn,hkp,b_return_exponent_lt B s hx n (t 1) hn he,he⟩

theorem xy_source_of_short_cut {H : NumericalSemigroup} (B : Base H)
    (hlive : (B.C-1)*B.triple.g 1∉B.K) (x y : ℕ)
    (hUF : ∀ e, B.triple.weight e=B.triple.weight (vector x y 0) → e=vector x y 0)
    (hK : B.triple.weight (vector x y 0)∈B.K) :
    ∃ s : B.Source, B.norm s≤vector x y 0 ∧ 0<B.norm s 0 ∧ B.norm s 2=0 := by
  obtain ⟨s,hs⟩ := cut_normal_source_divisor_of_unique B.triple B.m B.C B.u B.v B.tie
    (vector x y 0) hUF hK
  change B.norm s≤vector x y 0 at hs
  have h2 : B.norm s 2=0 := by have h := hs 2; simp at h; omega
  have h0 : 0<B.norm s 0 := by have h := normal_not_pure_y B hlive s; omega
  exact ⟨s,hs,h0,h2⟩

theorem yz_source_of_short_cut {H : NumericalSemigroup} (B : Base H)
    (hlive : (B.C-1)*B.triple.g 1∉B.K) (y z : ℕ)
    (hUF : ∀ e, B.triple.weight e=B.triple.weight (vector 0 y z) → e=vector 0 y z)
    (hK : B.triple.weight (vector 0 y z)∈B.K) :
    ∃ s : B.Source, B.norm s≤vector 0 y z ∧ B.norm s 0=0 ∧ 0<B.norm s 2 := by
  obtain ⟨s,hs⟩ := cut_normal_source_divisor_of_unique B.triple B.m B.C B.u B.v B.tie
    (vector 0 y z) hUF hK
  change B.norm s≤vector 0 y z at hs
  have h0 : B.norm s 0=0 := by have h := hs 0; simp at h; omega
  have h2 : 0<B.norm s 2 := by have h := normal_not_pure_y B hlive s; omega
  exact ⟨s,hs,h0,h2⟩

end NS25Lean.CriticalCapSources
