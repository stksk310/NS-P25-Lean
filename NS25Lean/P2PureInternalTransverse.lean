import NS25Lean.P2ErasedSourceScreen

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.PureInternalTransverse
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen

def vector (x y z : ℕ) : Exponent :=
  Finsupp.single 0 x+Finsupp.single 1 y+Finsupp.single 2 z

@[simp] theorem vector_zero (x y z : ℕ) : vector x y z 0=x := by simp [vector]
@[simp] theorem vector_one (x y z : ℕ) : vector x y z 1=y := by simp [vector]
@[simp] theorem vector_two (x y z : ℕ) : vector x y z 2=z := by simp [vector]

theorem vector_weight {H : NumericalSemigroup} (T : Triple H) (x y z : ℕ) :
    T.weight (vector x y z)=T.grid x y z := by
  simp only [vector,map_add,T.weight_single,Triple.grid]

/-- The standalone pure-internal transverse theorem. Normals are actual
source factorizations in O; the minimum and fiber-uniqueness assumptions are
exactly the paper's hypotheses, and no transverse attainment is assumed. -/
theorem transverse_minimum {H : NumericalSemigroup} (T : Triple H)
    (m : ℕ) (hm : 0<m) (C u : ℕ) (hC : 0<C) (hu : 0<u)
    (hrel : C*T.g 1=u*T.g 0)
    (O : Set Exponent)
    (normal : IdealSources H (cyclicCut H m)→Exponent)
    (normal_weight : ∀ s, T.weight (normal s)=s.val)
    (normal_mem : ∀ s, normal s∈O)
    (s : IdealSources H (cyclicCut H m))
    (hnf : s.val≠firstPrincipal H m hm*m)
    (i k : ℕ) (hi : 0< i) (hiu : i<u) (hk : 0<k)
    (hs : T.weight (vector i 0 k)=s.val)
    (hmin : ∀ g∈O, 0<g 2 → k≤g 2)
    (hUF : ∀ j<C, ∀ z : Exponent,
      T.weight z=T.weight (vector 0 j k) → z=vector 0 j k)
    (hlive : (C-1)*T.g 1∉cyclicCut H m) :
    ∃ t : IdealSources H (cyclicCut H m),
      normal t∈O ∧ normal t 0=0 ∧ normal t 2=k := by
  obtain ⟨n,r,hn,_,hr,hrp,hret⟩ := nonfirst_source_small_return H m hm s hnf
  let se : Sources H m Set.univ :=
    ⟨s.val,by simpa only [returnCut_univ] using s.property⟩
  obtain ⟨e,he⟩ := T.factor r hr
  have sep {j : Fin 3} (hsi : T.D s.val j) (hei : 0<e j) : False :=
    source_remainder_support_disjoint T m Set.univ se (Set.mem_univ n) hn hret hsi
      (he ▸ T.D_of_coordinate e j hei)
  have hs0 : T.D s.val 0 := hs ▸ T.D_of_coordinate (vector i 0 k) 0 (by simpa using hi)
  have hs2 : T.D s.val 2 := hs ▸ T.D_of_coordinate (vector i 0 k) 2 (by simpa using hk)
  have he0 : e 0=0 := by by_contra h; exact sep hs0 (by omega)
  have he2 : e 2=0 := by by_contra h; exact sep hs2 (by omega)
  have herb : r=e 1*T.g 1 := by
    simp only [T.weight_three,Triple.grid,he0,he2,zero_mul,zero_add,add_zero] at he
    exact he.symm
  have hj : 0<e 1 := by nlinarith
  have hjC : e 1<C := by
    by_contra hh
    have hle : C≤e 1 := by omega
    have hmj := congrArg (fun a => a*T.g 1) (Nat.sub_add_cancel hle)
    simp only [Nat.add_mul] at hmj
    have hnew : T.weight (vector u (e 1-C) 0)=r := by
      rw [vector_weight,Triple.grid]
      nlinarith only [hrel,hmj,herb]
    exact source_remainder_support_disjoint T m Set.univ se (Set.mem_univ n) hn hret hs0
      (hnew ▸ T.D_of_coordinate (vector u (e 1-C) 0) 0 (by simpa using hu))
  let M := vector 0 (C-e 1) k
  have htarget : T.weight M=n*m+(u-i)*T.g 0 := by
    have hmi := congrArg (fun a => a*T.g 0) (Nat.sub_add_cancel hiu.le)
    have hmj := congrArg (fun a => a*T.g 1) (Nat.sub_add_cancel hjC.le)
    simp only [Nat.add_mul] at hmi hmj
    rw [vector_weight,Triple.grid] at hs
    dsimp [M]
    rw [vector_weight,Triple.grid]
    nlinarith only [hrel,hs,hret,herb,hmi,hmj]
  have hK : T.weight M∈cyclicCut H m :=
    ⟨T.member M,n,hn,(u-i)*T.g 0,by
      simpa only [T.weight_single] using T.member (Finsupp.single 0 (u-i)),htarget⟩
  have hUnique : ∀ z, T.weight z=T.weight M → z=M :=
    hUF (C-e 1) (by omega)
  obtain ⟨t,g,hg,hle,huniq⟩ := unique_cut_literal_source_divisor H (cyclicCut H m)
    (fun _ h => h.1) T.weight T.factor M hK hUnique
  have hnrel : normal t=g := huniq (normal t) (normal_weight t)
  have hg0 : g 0=0 := by have := hle 0; simp [M] at this; omega
  have hgk : g 2≤k := by simpa [M] using hle 2
  have hgp : 0<g 2 := by
    by_contra hh
    have hg2 : g 2=0 := by omega
    have hgy : g 1<C := by have h := hle 1; simp [M] at h; omega
    have hgb : T.weight g=g 1*T.g 1 := by
      simp only [T.weight_three,Triple.grid,hg0,hg2,zero_mul,zero_add,add_zero]
    have hcut : g 1*T.g 1∈cyclicCut H m := by rw [←hgb,hg]; exact t.property.1
    have hd := T.member (Finsupp.single 1 (C-1-g 1))
    rw [T.weight_single] at hd
    have hcut' := ErasedSourceScreen.cut_add H hcut hd
    have heq : g 1*T.g 1+(C-1-g 1)*T.g 1=(C-1)*T.g 1 := by
      rw [←Nat.add_mul,Nat.add_sub_of_le (by omega)]
    exact hlive (heq ▸ hcut')
  refine ⟨t,normal_mem t,by rw [hnrel]; exact hg0,?_⟩
  have hlow := hmin (normal t) (normal_mem t) (by rw [hnrel]; exact hgp)
  rw [hnrel] at hlow ⊢
  omega

end NS25Lean.PureInternalTransverse
