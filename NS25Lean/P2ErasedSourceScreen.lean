import NS25Lean.P2ReturnExchange

set_option autoImplicit false
set_option linter.style.header false
noncomputable section

namespace NS25Lean.ErasedSourceScreen
open FourGeneratedBridge L5A2C4OR19 ReturnExchange
abbrev Exponent := Fin 3→₀ℕ

/-- Exactly a positive three-generator presentation of the same numerical H. -/
structure Triple (H : NumericalSemigroup) where
  weight : Exponent→+ℕ
  positive : ∀ i, 0<weight (Finsupp.single i 1)
  member : ∀ e, weight e∈H
  factor : ∀ h∈H, ∃ e, weight e=h

def Triple.g {H : NumericalSemigroup} (T : Triple H) (i : Fin 3) : ℕ :=
  T.weight (Finsupp.single i 1)

theorem Triple.weight_single {H : NumericalSemigroup} (T : Triple H)
    (i : Fin 3) (n : ℕ) : T.weight (Finsupp.single i n)=n*T.g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (Finsupp.single i (n+1) : Exponent)=
        Finsupp.single i n+Finsupp.single i 1 := by simp
    rw [he,map_add,ih]
    change n*T.g i+T.g i=(n+1)*T.g i
    ring

theorem Triple.weight_split {H : NumericalSemigroup} (T : Triple H)
    (e : Exponent) (i : Fin 3) : T.weight e=e i*T.g i+T.weight (e.erase i) := by
  conv_lhs => rw [←Finsupp.single_add_erase i e,map_add,T.weight_single]

theorem Triple.weight_eq_zero {H : NumericalSemigroup} (T : Triple H)
    {e : Exponent} (he : T.weight e=0) : e=0 := by
  ext i
  have hs := T.weight_split e i
  have hp := T.positive i
  change 0<T.g i at hp
  simp only [Finsupp.zero_apply]
  nlinarith

/-- D is union support over all factorizations, not support of one chosen vector. -/
def Triple.D {H : NumericalSemigroup} (T : Triple H) (h : ℕ) (i : Fin 3) : Prop :=
  ∃ p∈H, h=p+T.g i

theorem Triple.D_of_coordinate {H : NumericalSemigroup} (T : Triple H)
    (e : Exponent) (i : Fin 3) (hi : 0<e i) : T.D (T.weight e) i := by
  let r := Finsupp.single i (e i-1)+e.erase i
  refine ⟨T.weight r,T.member r,?_⟩
  have hs := T.weight_split e i
  have hm := congrArg (fun n => n*T.g i) (show e i-1+1=e i by omega)
  simp only [Nat.add_mul,one_mul] at hm
  dsimp [r]
  rw [map_add,T.weight_single]
  omega

theorem Triple.factor_of_D {H : NumericalSemigroup} (T : Triple H)
    {h : ℕ} {i : Fin 3} (hi : T.D h i) :
    ∃ e : Exponent, T.weight e=h ∧ 0<e i := by
  obtain ⟨p,hp,he⟩ := hi
  obtain ⟨e,he'⟩ := T.factor p hp
  refine ⟨e+Finsupp.single i 1,?_,by simp⟩
  rw [map_add,he']
  exact he.symm

theorem Triple.D_nonempty {H : NumericalSemigroup} (T : Triple H)
    {h : ℕ} (hh : h∈H) (hp : 0<h) : ∃ i, T.D h i := by
  obtain ⟨e,he⟩ := T.factor h hh
  by_contra hn
  push Not at hn
  have he0 : e=0 := by
    ext i
    have hi : ¬0<e i := fun hi => hn i (he ▸ T.D_of_coordinate e i hi)
    simpa using (show e i=0 by omega)
  simp [he0] at he
  omega

theorem Triple.pure_of_support {H : NumericalSemigroup} (T : Triple H)
    {h : ℕ} (hh : h∈H) (hp : 0<h) (i : Fin 3)
    (hs : ∀ j, j≠i → ¬T.D h j) : ∃ n, 0<n ∧ h=n*T.g i := by
  obtain ⟨e,he⟩ := T.factor h hh
  have heq : e=Finsupp.single i (e i) := by
    ext j
    by_cases hj : j=i
    · subst j; simp
    · have hz : e j=0 := by
        by_contra hn
        exact hs j hj (he ▸ T.D_of_coordinate e j (by omega))
      simp [hj,hz]
  rw [heq,T.weight_single] at he
  exact ⟨e i,by nlinarith,he.symm⟩

/-- True least outside exponents, specified by actual relations and minimality. -/
structure Critical {H : NumericalSemigroup} (T : Triple H) where
  exponent : Fin 3→ℕ
  positive : ∀ i, 0<exponent i
  outside : ∀ i, ∃ e : Exponent, e i=0 ∧ T.weight e=exponent i*T.g i
  least : ∀ i n (e : Exponent), 0<n → e i=0 →
    n*T.g i=T.weight e → exponent i≤n

theorem Critical.subcritical_unique {H : NumericalSemigroup} {T : Triple H}
    (C : Critical T) (i : Fin 3) {n : ℕ} (hn : n<C.exponent i)
    (e : Exponent) (he : T.weight e=n*T.g i) : e=Finsupp.single i n := by
  have hs := T.weight_split e i
  have hp := T.positive i
  change 0<T.g i at hp
  have hi : e i≤n := by nlinarith
  by_cases hil : e i<n
  · have hm := congrArg (fun t => t*T.g i) (Nat.sub_add_cancel hi)
    simp only [Nat.add_mul] at hm
    have hc := C.least i (n-e i) (e.erase i) (by omega) (by simp)
      (by nlinarith : (n-e i)*T.g i=T.weight (e.erase i))
    omega
  · have hieq : e i=n := by omega
    have hz : T.weight (e.erase i)=0 := by nlinarith
    have her := T.weight_eq_zero hz
    have hrec := Finsupp.single_add_erase i e
    simpa [her,hieq] using hrec.symm

theorem Critical.pure_support_bound {H : NumericalSemigroup} {T : Triple H}
    (C : Critical T) (i : Fin 3) {h n : ℕ} (he : h=n*T.g i)
    (hs : ∀ j, j≠i → ¬T.D h j) : n<C.exponent i := by
  by_contra hn
  obtain ⟨e,hei,hew⟩ := C.outside i
  let f : Exponent := e+Finsupp.single i (n-C.exponent i)
  have hf : T.weight f=h := by
    dsimp [f]
    rw [map_add,T.weight_single,hew,he,←Nat.add_mul,Nat.add_sub_of_le (by omega)]
  have hfi : f i=n-C.exponent i := by simp [f,hei]
  have hfeq : f=Finsupp.single i (n-C.exponent i) := by
    ext j
    by_cases hj : j=i
    · subst j; simp [hfi]
    · have hz : f j=0 := by
        by_contra hh
        exact hs j hj (hf ▸ T.D_of_coordinate f j (by omega))
      simp [hj,hz]
  have he0 : e=0 := by
    ext j
    have hh := congrArg (fun v : Exponent => v j) hfeq
    simp only [f,Finsupp.add_apply] at hh
    simpa using (show e j=0 by omega)
  have hc := C.positive i
  have hg := T.positive i
  change 0<T.g i at hg
  simp [he0] at hew
  rcases hew with hz | hz <;> omega

theorem Critical.subcritical_D_only {H : NumericalSemigroup} {T : Triple H}
    (C : Critical T) (i : Fin 3) {n : ℕ} (hn : n<C.exponent i)
    {j : Fin 3} (hj : j≠i) : ¬T.D (n*T.g i) j := by
  intro hd
  obtain ⟨e,he,hej⟩ := T.factor_of_D hd
  have hu := C.subcritical_unique i hn e he
  rw [hu,Finsupp.single_eq_of_ne hj] at hej
  omega

theorem source_remainder_support_disjoint {H : NumericalSemigroup}
    (T : Triple H) (m : ℕ) (E : Set ℕ) (s : Sources H m E)
    {n r : ℕ} (hn : n∈E) (hp : 0<n) (he : s.val=n*m+r)
    {i : Fin 3} (hs : T.D s.val i) (hr : T.D r i) : False := by
  obtain ⟨z,hz,hs⟩ := hs
  obtain ⟨y,hy,hr⟩ := hr
  have hh := source_return_separation H m E s hn hp hy hz
    (T.member (Finsupp.single i 1)) hs (by omega : s.val=n*m+(y+T.g i))
  have hg := T.positive i
  change 0<T.g i at hg
  change T.g i=0 at hh
  omega

def Erased {H : NumericalSemigroup} (m Q : ℕ) {E : Set ℕ}
    (s : Sources H m E) : Prop := ∃ d∈H, s.val=Q*m+d

theorem cut_add (H : NumericalSemigroup) {m x d : ℕ}
    (hx : x∈cyclicCut H m) (hd : d∈H) : x+d∈cyclicCut H m := by
  obtain ⟨hx,n,hn,r,hr,he⟩ := hx
  exact ⟨H.add_mem hx hd,n,hn,r+d,H.add_mem hr hd,by omega⟩

theorem below_live_not_cut {H : NumericalSemigroup} {T : Triple H}
    (C : Critical T) (m : ℕ) (i : Fin 3)
    (hlive : (C.exponent i-1)*T.g i∉cyclicCut H m)
    {n : ℕ} (hn : n<C.exponent i) : n*T.g i∉cyclicCut H m := by
  intro h
  have hd := T.member (Finsupp.single i (C.exponent i-1-n))
  rw [T.weight_single] at hd
  have hh := cut_add H h hd
  have he : n*T.g i+(C.exponent i-1-n)*T.g i=(C.exponent i-1)*T.g i := by
    rw [←Nat.add_mul,Nat.add_sub_of_le (by omega)]
  exact hlive (he ▸ hh)

theorem erased_remainder {H : NumericalSemigroup} (m : ℕ) (hm : 0<m)
    (E : Set ℕ) (hE : ∀ n∈E, n<firstPrincipal H m hm)
    (s : Sources H m E) (hs : Erased m (firstPrincipal H m hm) s) :
    ∃ n∈E, ∃ r∈H, 0<n ∧ n<firstPrincipal H m hm ∧ 0<r ∧
      r∈cyclicCut H m ∧ s.val=n*m+r := by
  obtain ⟨hsH,n,hn,hp,r,hr,he⟩ := s.property.1
  obtain ⟨d,hd,hdiv⟩ := hs
  exact ⟨n,hn,r,hr,hp,hE n hn,small_return_positive H m hm hsH hp (hE n hn) he,
    cyclic_erasure_reflection H m _ s.val n r d (hE n hn) hr hd he hdiv,he⟩

theorem support_mono {H : NumericalSemigroup} (T : Triple H)
    {h f d : ℕ} (hd : d∈H) (he : h=f+d) {i : Fin 3}
    (hi : T.D f i) : T.D h i := by
  obtain ⟨p,hp,hp'⟩ := hi
  exact ⟨p+d,H.add_mem hp hd,by omega⟩

theorem singleton_erasure_impossible {H : NumericalSemigroup} {T : Triple H}
    (C : Critical T) (m : ℕ) (hm : 0<m) (E : Set ℕ)
    (s : Sources H m E) (hs : Erased m (firstPrincipal H m hm) s)
    (i : Fin 3) (hlive : (C.exponent i-1)*T.g i∉cyclicCut H m)
    (hpos : 0<s.val) (hsupp : ∀ j, j≠i → ¬T.D s.val j) : False := by
  obtain ⟨n,hn,he⟩ := T.pure_of_support s.property.1.1 hpos i hsupp
  have hnc := C.pure_support_bound i he hsupp
  obtain ⟨d,hd,hdiv⟩ := hs
  have fpos : 0<firstPrincipal H m hm*m := by
    exact Nat.mul_pos (firstPrincipal_spec H m hm).1 hm
  have fsupp : ∀ j, j≠i → ¬T.D (firstPrincipal H m hm*m) j := by
    intro j hj hjd
    exact hsupp j hj (support_mono T hd hdiv hjd)
  obtain ⟨k,hk,hke⟩ := T.pure_of_support (firstPrincipal_spec H m hm).2 fpos i fsupp
  have hg := T.positive i
  change 0<T.g i at hg
  have hkn : k≤n := by nlinarith [show k*T.g i≤n*T.g i by omega]
  have hcut := (firstPrincipal_minimal_cut_source H m hm).1
  rw [hke] at hcut
  exact below_live_not_cut C m i hlive (by omega) hcut

theorem remainder_singleton_impossible {H : NumericalSemigroup} {T : Triple H}
    (C : Critical T) (m r : ℕ) (hr : r∈H) (hp : 0<r)
    (hK : r∈cyclicCut H m) (i : Fin 3)
    (hlive : (C.exponent i-1)*T.g i∉cyclicCut H m)
    (hsupp : ∀ j, j≠i → ¬T.D r j) : False := by
  obtain ⟨n,hn,he⟩ := T.pure_of_support hr hp i hsupp
  have hc := C.pure_support_bound i he hsupp
  exact below_live_not_cut C m i hlive hc (he ▸ hK)

/-- Part (1) of the common erasure screen, for every gap-return subfamily. -/
theorem no_erasure_of_three_live {H : NumericalSemigroup} {T : Triple H}
    (C : Critical T) (m : ℕ) (hm : 0<m) (E : Set ℕ)
    (hE : ∀ n∈E, n<firstPrincipal H m hm)
    (hlive : ∀ i, (C.exponent i-1)*T.g i∉cyclicCut H m)
    (s : Sources H m E) : ¬Erased m (firstPrincipal H m hm) s := by
  intro hs
  obtain ⟨n,hn,r,hr,hp,_,hrp,hrK,he⟩ := erased_remainder m hm E hE s hs
  have hsp : 0<s.val := by nlinarith
  have disj {i : Fin 3} (hi : T.D s.val i) (hj : T.D r i) : False :=
    source_remainder_support_disjoint T m E s hn hp he hi hj
  have single (i : Fin 3) (h : ∀ j, j≠i → ¬T.D s.val j) : False :=
    singleton_erasure_impossible C m hm E s hs i (hlive i) hsp h
  have pair (i : Fin 3) (h : ∀ j, j≠i → T.D s.val j) : False := by
    apply remainder_singleton_impossible C m r hr hrp hrK i (hlive i)
    intro j hj hd
    exact disj (h j hj) hd
  by_cases h0 : T.D s.val 0 <;> by_cases h1 : T.D s.val 1 <;>
      by_cases h2 : T.D s.val 2
  · obtain ⟨i,hi⟩ := T.D_nonempty hr hrp
    fin_cases i <;> exact disj (by assumption) hi
  · exact pair 2 (by intro j hj; fin_cases j <;> simp_all)
  · exact pair 1 (by intro j hj; fin_cases j <;> simp_all)
  · exact single 0 (by intro j hj; fin_cases j <;> simp_all)
  · exact pair 0 (by intro j hj; fin_cases j <;> simp_all)
  · exact single 1 (by intro j hj; fin_cases j <;> simp_all)
  · exact single 2 (by intro j hj; fin_cases j <;> simp_all)
  · obtain ⟨i,hi⟩ := T.D_nonempty s.property.1.1 hsp
    fin_cases i <;> contradiction

def Triple.grid {H : NumericalSemigroup} (T : Triple H) (x y z : ℕ) : ℕ :=
  x*T.g 0+y*T.g 1+z*T.g 2

theorem Triple.grid_mem {H : NumericalSemigroup} (T : Triple H) (x y z : ℕ) :
    T.grid x y z∈H := by
  have h := T.member (Finsupp.single 0 x+Finsupp.single 1 y+Finsupp.single 2 z)
  simpa only [map_add,T.weight_single,Triple.grid] using h

theorem Triple.weight_three {H : NumericalSemigroup} (T : Triple H) (e : Exponent) :
    T.weight e=T.grid (e 0) (e 1) (e 2) := by
  have he : e=Finsupp.single 0 (e 0)+Finsupp.single 1 (e 1)+Finsupp.single 2 (e 2) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [he]
  simp only [map_add,T.weight_single,Triple.grid]

/-- The coherent identities are supplied by the genuine critical-presentation
theorem, independently of all return/source assertions. -/
structure PositivePresentation {H : NumericalSemigroup} {T : Triple H} (C : Critical T) where
  P : ℕ
  Q : ℕ
  U : ℕ
  V : ℕ
  W : ℕ
  Z : ℕ
  positive : 0<P ∧ 0<Q ∧ 0<U ∧ 0<V ∧ 0<W ∧ 0<Z
  relationA : C.exponent 0*T.g 0=P*T.g 1+Q*T.g 2
  relationB : C.exponent 1*T.g 1=U*T.g 0+V*T.g 2
  relationC : C.exponent 2*T.g 2=W*T.g 0+Z*T.g 1
  coherentB : C.exponent 1=P+Z
  coherentC : C.exponent 2=Q+V

theorem PositivePresentation.grid_bounds {H : NumericalSemigroup} {T : Triple H}
    {C : Critical T} (D : PositivePresentation C) {h i j : ℕ}
    (ha : ¬T.D h 0) (he : h=i*T.g 1+j*T.g 2) :
    i<C.exponent 1 ∧ j<C.exponent 2 ∧ (i<D.P ∨ j<D.Q) := by
  have hp := D.positive
  have hb : i<C.exponent 1 := by
    by_contra hn
    have hle : C.exponent 1≤ i := by omega
    have hm := congrArg (fun n => n*T.g 1) (Nat.sub_add_cancel hle)
    simp only [Nat.add_mul] at hm
    have hu := congrArg (fun n => n*T.g 0) (show D.U-1+1=D.U by omega)
    simp only [Nat.add_mul,one_mul] at hu
    apply ha
    refine ⟨T.grid (D.U-1) (i-C.exponent 1) (j+D.V),T.grid_mem _ _ _,?_⟩
    dsimp [Triple.grid]
    nlinarith only [he,D.relationB,hm,hu]
  have hc : j<C.exponent 2 := by
    by_contra hn
    have hle : C.exponent 2≤ j := by omega
    have hm := congrArg (fun n => n*T.g 2) (Nat.sub_add_cancel hle)
    simp only [Nat.add_mul] at hm
    have hw := congrArg (fun n => n*T.g 0) (show D.W-1+1=D.W by omega)
    simp only [Nat.add_mul,one_mul] at hw
    apply ha
    refine ⟨T.grid (D.W-1) (i+D.Z) (j-C.exponent 2),T.grid_mem _ _ _,?_⟩
    dsimp [Triple.grid]
    nlinarith only [he,D.relationC,hm,hw]
  refine ⟨hb,hc,?_⟩
  by_contra hn
  push Not at hn
  have hmi := congrArg (fun n => n*T.g 1) (Nat.sub_add_cancel hn.1)
  have hmj := congrArg (fun n => n*T.g 2) (Nat.sub_add_cancel hn.2)
  have hma := congrArg (fun n => n*T.g 0)
    (show C.exponent 0-1+1=C.exponent 0 by have := C.positive 0; omega)
  simp only [Nat.add_mul,one_mul] at hmi hmj hma
  apply ha
  refine ⟨T.grid (C.exponent 0-1) (i-D.P) (j-D.Q),T.grid_mem _ _ _,?_⟩
  dsimp [Triple.grid]
  nlinarith only [he,D.relationA,hmi,hmj,hma]

theorem PositivePresentation.bc_factor {H : NumericalSemigroup} {T : Triple H}
    {C : Critical T} (D : PositivePresentation C) {h : ℕ} (hh : h∈H)
    (ha : ¬T.D h 0) (hb : T.D h 1) (hc : T.D h 2) :
    ∃ i j, 0< i ∧ 0< j ∧ i<C.exponent 1 ∧ j<C.exponent 2 ∧
      (i<D.P ∨ j<D.Q) ∧ h=i*T.g 1+j*T.g 2 := by
  obtain ⟨e,he⟩ := T.factor h hh
  have hx : e 0=0 := by
    by_contra hn
    exact ha (he ▸ T.D_of_coordinate e 0 (by omega))
  have he' : h=e 1*T.g 1+e 2*T.g 2 := by
    rw [T.weight_three,Triple.grid,hx,zero_mul,zero_add] at he
    exact he.symm
  have hbnd := D.grid_bounds ha he'
  have hy : 0<e 1 := by
    by_contra hn
    have hz : e 1=0 := by omega
    have hec : h=e 2*T.g 2 := by simpa [hz] using he'
    exact C.subcritical_D_only 2 hbnd.2.1 (by decide : (1:Fin 3)≠2) (hec ▸ hb)
  have hz : 0<e 2 := by
    by_contra hn
    have hz : e 2=0 := by omega
    have heb : h=e 1*T.g 1 := by simpa [hz] using he'
    exact C.subcritical_D_only 1 hbnd.1 (by decide : (2:Fin 3)≠1) (heb ▸ hc)
  exact ⟨e 1,e 2,hy,hz,hbnd.1,hbnd.2.1,hbnd.2.2,he'⟩

theorem PositivePresentation.bc_erasure_impossible {H : NumericalSemigroup}
    {T : Triple H} {C : Critical T} (D : PositivePresentation C)
    (m : ℕ) (E : Set ℕ) (s : Sources H m E)
    {n r : ℕ} (hn : n∈E) (hp : 0<n) (hr : r∈H) (hrp : 0<r)
    (hrK : r∈cyclicCut H m) (he : s.val=n*m+r)
    (ha : ¬T.D s.val 0) (hb : T.D s.val 1) (hc : T.D s.val 2)
    (hlb : (C.exponent 1-1)*T.g 1∉cyclicCut H m)
    (hlc : (C.exponent 2-1)*T.g 2∉cyclicCut H m)
    (hlU : T.grid (D.U-1) 0 D.V∉cyclicCut H m)
    (hlW : T.grid (D.W-1) D.Z 0∉cyclicCut H m) : False := by
  have disj {i : Fin 3} (hi : T.D s.val i) (hj : T.D r i) : False :=
    source_remainder_support_disjoint T m E s hn hp he hi hj
  obtain ⟨d,hd,hdr⟩ := T.pure_of_support hr hrp 0 (by
    intro j hj
    fin_cases j
    · contradiction
    · exact fun h => disj hb h
    · exact fun h => disj hc h)
  obtain ⟨i,j,hi,hj,hiB,hjC,hregion,hsij⟩ := D.bc_factor s.property.1.1 ha hb hc
  have hret : i*T.g 1+j*T.g 2=n*m+d*T.g 0 := by omega
  have hpositive := D.positive
  have useT (hjt : j<D.Q) : False := by
    by_cases hdu : D.U≤d
    · have hdm := congrArg (fun k => k*T.g 0) (Nat.sub_add_cancel hdu)
      have him := congrArg (fun k => k*T.g 1) (Nat.sub_add_cancel hiB.le)
      simp only [Nat.add_mul] at hdm him
      have hcut : (j+D.V)*T.g 2∈cyclicCut H m := by
        refine ⟨by simpa only [Triple.grid,zero_mul,zero_add] using T.grid_mem 0 0 (j+D.V),
          n,hp,T.grid (d-D.U) (C.exponent 1-i) 0,T.grid_mem _ _ _,?_⟩
        dsimp [Triple.grid]
        nlinarith only [hret,D.relationB,hdm,him]
      exact below_live_not_cut C m 2 hlc (by rw [D.coherentC]; omega) hcut
    · have hrd : d<D.U := by omega
      have hcut := cut_add H hrK (T.grid_mem (D.U-1-d) 0 D.V)
      apply hlU
      have hdm := congrArg (fun k => k*T.g 0)
        (show d+(D.U-1-d)=D.U-1 by omega)
      simp only [Nat.add_mul] at hdm
      convert hcut using 1 <;> dsimp [Triple.grid] <;> omega
  have useP (hip : i<D.P) : False := by
    by_cases hdw : D.W≤d
    · have hdm := congrArg (fun k => k*T.g 0) (Nat.sub_add_cancel hdw)
      have hjm := congrArg (fun k => k*T.g 2) (Nat.sub_add_cancel hjC.le)
      simp only [Nat.add_mul] at hdm hjm
      have hcut : (i+D.Z)*T.g 1∈cyclicCut H m := by
        refine ⟨by simpa only [Triple.grid,zero_mul,zero_add,add_zero] using T.grid_mem 0 (i+D.Z) 0,
          n,hp,T.grid (d-D.W) 0 (C.exponent 2-j),T.grid_mem _ _ _,?_⟩
        dsimp [Triple.grid]
        nlinarith only [hret,D.relationC,hdm,hjm]
      exact below_live_not_cut C m 1 hlb (by rw [D.coherentB]; omega) hcut
    · have hrd : d<D.W := by omega
      have hcut := cut_add H hrK (T.grid_mem (D.W-1-d) D.Z 0)
      apply hlW
      have hdm := congrArg (fun k => k*T.g 0)
        (show d+(D.W-1-d)=D.W-1 by omega)
      simp only [Nat.add_mul] at hdm
      convert hcut using 1 <;> dsimp [Triple.grid] <;> omega
  exact hregion.elim useP useT

/-- Four live critical predecessors force every erased E-source onto the
subcritical pure-a chain. E is arbitrary, including the empty set. -/
theorem erased_source_pure_a {H : NumericalSemigroup} {T : Triple H}
    {C : Critical T} (D : PositivePresentation C) (m : ℕ) (hm : 0<m)
    (E : Set ℕ) (hE : ∀ n∈E, n<firstPrincipal H m hm)
    (hlb : (C.exponent 1-1)*T.g 1∉cyclicCut H m)
    (hlU : T.grid (D.U-1) 0 D.V∉cyclicCut H m)
    (hlc : (C.exponent 2-1)*T.g 2∉cyclicCut H m)
    (hlW : T.grid (D.W-1) D.Z 0∉cyclicCut H m)
    (s : Sources H m E) (hs : Erased m (firstPrincipal H m hm) s) :
    ∃ a, 0<a ∧ a<C.exponent 0 ∧ s.val=a*T.g 0 := by
  obtain ⟨n,hn,r,hr,hp,_,hrp,hrK,he⟩ := erased_remainder m hm E hE s hs
  have hsp : 0<s.val := by nlinarith
  have disj {i : Fin 3} (hi : T.D s.val i) (hj : T.D r i) : False :=
    source_remainder_support_disjoint T m E s hn hp he hi hj
  have pair (i : Fin 3) (hl : (C.exponent i-1)*T.g i∉cyclicCut H m)
      (h : ∀ j, j≠i → T.D s.val j) : False := by
    apply remainder_singleton_impossible C m r hr hrp hrK i hl
    intro j hj hd
    exact disj (h j hj) hd
  have single (i : Fin 3) (hl : (C.exponent i-1)*T.g i∉cyclicCut H m)
      (h : ∀ j, j≠i → ¬T.D s.val j) : False :=
    singleton_erasure_impossible C m hm E s hs i hl hsp h
  have hsupport : ∀ j, j≠(0:Fin 3) → ¬T.D s.val j := by
    by_cases h0 : T.D s.val 0
    · intro j hj hd
      fin_cases j
      · contradiction
      · exact pair 2 hlc (by intro i hi; fin_cases i <;> simp_all)
      · exact pair 1 hlb (by intro i hi; fin_cases i <;> simp_all)
    · by_cases h1 : T.D s.val 1
      · by_cases h2 : T.D s.val 2
        · exact (D.bc_erasure_impossible m E s hn hp hr hrp hrK he h0 h1 h2
            hlb hlc hlU hlW).elim
        · exact (single 1 hlb (by intro i hi; fin_cases i <;> simp_all)).elim
      · by_cases h2 : T.D s.val 2
        · exact (single 2 hlc (by intro i hi; fin_cases i <;> simp_all)).elim
        · obtain ⟨i,hi⟩ := T.D_nonempty s.property.1.1 hsp
          fin_cases i <;> contradiction
  obtain ⟨a,ha,hea⟩ := T.pure_of_support s.property.1.1 hsp 0 hsupport
  exact ⟨a,ha,C.pure_support_bound 0 hea hsupport,hea⟩

theorem erased_principal_pure_a {H : NumericalSemigroup} {T : Triple H}
    {C : Critical T} (D : PositivePresentation C) (m : ℕ) (hm : 0<m)
    (E : Set ℕ) (hE : ∀ n∈E, n<firstPrincipal H m hm)
    (hlb : (C.exponent 1-1)*T.g 1∉cyclicCut H m)
    (hlU : T.grid (D.U-1) 0 D.V∉cyclicCut H m)
    (hlc : (C.exponent 2-1)*T.g 2∉cyclicCut H m)
    (hlW : T.grid (D.W-1) D.Z 0∉cyclicCut H m)
    (s : Sources H m E) (hs : Erased m (firstPrincipal H m hm) s) :
    ∃ k, 0<k ∧ k<C.exponent 0 ∧ firstPrincipal H m hm*m=k*T.g 0 := by
  obtain ⟨a,ha,haC,he⟩ := erased_source_pure_a D m hm E hE hlb hlU hlc hlW s hs
  obtain ⟨d,hd,hdiv⟩ := hs
  have hsupport : ∀ j, j≠(0:Fin 3) → ¬T.D (firstPrincipal H m hm*m) j := by
    intro j hj hD
    have hsD := support_mono T hd hdiv hD
    apply C.subcritical_D_only 0 haC hj
    exact he ▸ hsD
  have hfpos := Nat.mul_pos (firstPrincipal_spec H m hm).1 hm
  obtain ⟨k,hk,hek⟩ := T.pure_of_support (firstPrincipal_spec H m hm).2 hfpos 0 hsupport
  have hg := T.positive 0
  change 0<T.g 0 at hg
  have hka : k≤a := by nlinarith [show k*T.g 0≤a*T.g 0 by omega]
  exact ⟨k,hk,lt_of_le_of_lt hka haC,hek⟩

theorem erased_sources_subsingleton {H : NumericalSemigroup} {T : Triple H}
    {C : Critical T} (D : PositivePresentation C) (m : ℕ) (hm : 0<m)
    (E : Set ℕ) (hE : ∀ n∈E, n<firstPrincipal H m hm)
    (hlb : (C.exponent 1-1)*T.g 1∉cyclicCut H m)
    (hlU : T.grid (D.U-1) 0 D.V∉cyclicCut H m)
    (hlc : (C.exponent 2-1)*T.g 2∉cyclicCut H m)
    (hlW : T.grid (D.W-1) D.Z 0∉cyclicCut H m) :
    Subsingleton {s : Sources H m E // Erased m (firstPrincipal H m hm) s} := by
  refine ⟨?_⟩
  intro s t
  obtain ⟨a,_,_,ha⟩ := erased_source_pure_a D m hm E hE hlb hlU hlc hlW s.val s.property
  obtain ⟨b,_,_,hb⟩ := erased_source_pure_a D m hm E hE hlb hlU hlc hlW t.val t.property
  have comparable {a b : ℕ} (ha : s.val.val=a*T.g 0) (hb : t.val.val=b*T.g 0)
      (hab : a≤b) : s.val.val=t.val.val := by
    have hd := T.member (Finsupp.single 0 (b-a))
    rw [T.weight_single] at hd
    have he : t.val.val=s.val.val+(b-a)*T.g 0 := by
      rw [ha,hb,←Nat.add_mul,Nat.add_sub_of_le hab]
    have hz := ((minimal_iff_literal H _ _).mp t.val.property).2
      s.val.val ((b-a)*T.g 0) s.val.property.1 hd he
    omega
  have heq : s.val.val=t.val.val := by
    rcases le_total a b with hab | hba
    · exact comparable ha hb hab
    · have hd := T.member (Finsupp.single 0 (a-b))
      rw [T.weight_single] at hd
      have he : s.val.val=t.val.val+(a-b)*T.g 0 := by
        rw [ha,hb,←Nat.add_mul,Nat.add_sub_of_le hba]
      have hz := ((minimal_iff_literal H _ _).mp s.val.property).2
        t.val.val ((a-b)*T.g 0) t.val.property.1 hd he
      omega
  exact Subtype.ext (Subtype.ext heq)

theorem erased_source_count_le_one {H : NumericalSemigroup} {T : Triple H}
    {C : Critical T} (D : PositivePresentation C) (m : ℕ) (hm : 0<m)
    (E : Set ℕ) (hE : ∀ n∈E, n<firstPrincipal H m hm)
    (hlb : (C.exponent 1-1)*T.g 1∉cyclicCut H m)
    (hlU : T.grid (D.U-1) 0 D.V∉cyclicCut H m)
    (hlc : (C.exponent 2-1)*T.g 2∉cyclicCut H m)
    (hlW : T.grid (D.W-1) D.Z 0∉cyclicCut H m) :
    Nat.card {s : Sources H m E // Erased m (firstPrincipal H m hm) s}≤1 := by
  letI := erased_sources_subsingleton D m hm E hE hlb hlU hlc hlW
  simpa using Nat.card_le_card_of_injective
    (fun _ : {s : Sources H m E // Erased m (firstPrincipal H m hm) s} => ())
    (fun _ _ _ => Subsingleton.elim _ _)

/-- The coefficient t is integral. Its nonpositive branch obstructs Q-minimality;
its positive branch is an actual subcritical pure return. -/
theorem integer_complement_obstruction {H : NumericalSemigroup} {T : Triple H}
    (C : Critical T) (m : ℕ) (hm : 0<m) (i : Fin 3)
    (hlive : (C.exponent i-1)*T.g i∉cyclicCut H m)
    (q ell : ℕ) (hq : 0<q) (hqQ : q<firstPrincipal H m hm)
    (hell : ell<C.exponent i) (t : ℤ)
    (he : ((ell*T.g i : ℕ) : ℤ)=
      (((firstPrincipal H m hm-q)*m : ℕ) : ℤ)+t*T.g 0) : False := by
  have hcomp : 0<firstPrincipal H m hm-q := by omega
  have hcompQ : firstPrincipal H m hm-q<firstPrincipal H m hm := by omega
  by_cases ht : t≤0
  · have htn : (((-t).toNat : ℕ) : ℤ)=-t := Int.toNat_of_nonneg (by omega)
    have hsum : (firstPrincipal H m hm-q)*m=
        ell*T.g i+(-t).toNat*T.g 0 := by
      exact_mod_cast (show ((((firstPrincipal H m hm-q)*m : ℕ) : ℤ))=
        (ell:ℤ)*T.g i+(((-t).toNat:ℕ):ℤ)*T.g 0 by
          push_cast at he ⊢; nlinarith only [he,htn])
    have hmem := H.add_mem (T.member (Finsupp.single i ell))
      (T.member (Finsupp.single 0 (-t).toNat))
    rw [T.weight_single,T.weight_single,←hsum] at hmem
    have hmin := firstPrincipal_le H m hm hcomp hmem
    omega
  · have htn : ((t.toNat : ℕ) : ℤ)=t := Int.toNat_of_nonneg (by omega)
    have hsum : ell*T.g i=(firstPrincipal H m hm-q)*m+t.toNat*T.g 0 := by
      exact_mod_cast (show ((ell*T.g i:ℕ):ℤ)=
        (((firstPrincipal H m hm-q)*m:ℕ):ℤ)+(t.toNat:ℤ)*T.g 0 by
          rw [htn]; exact he)
    have hmem := T.member (Finsupp.single i ell)
    have hrem := T.member (Finsupp.single 0 t.toNat)
    rw [T.weight_single] at hmem hrem
    exact below_live_not_cut C m i hlive hell
      ⟨hmem,firstPrincipal H m hm-q,hcomp,_,hrem,hsum⟩

theorem pure_principal_forbids_integral_boundaries {H : NumericalSemigroup}
    {T : Triple H} {C : Critical T} (D : PositivePresentation C)
    (m : ℕ) (hm : 0<m)
    (hlb : (C.exponent 1-1)*T.g 1∉cyclicCut H m)
    (hlc : (C.exponent 2-1)*T.g 2∉cyclicCut H m)
    (k : ℕ) (hf : firstPrincipal H m hm*m=k*T.g 0)
    (q : ℕ) (hq : 0<q) (hqQ : q<firstPrincipal H m hm) (d : ℤ) :
    (∀ j : ℕ, j<D.Q →
      (q:ℤ)*m+d*T.g 0≠D.P*T.g 1+(j:ℤ)*T.g 2) ∧
    (∀ j : ℕ, j<D.P →
      (q:ℤ)*m+d*T.g 0≠(j:ℤ)*T.g 1+D.Q*T.g 2) := by
  have hqm := congrArg (fun n => n*m)
    (Nat.sub_add_cancel (Nat.le_of_lt hqQ))
  have hqmi : ((((firstPrincipal H m hm-q)*m+q*m:ℕ)):ℤ)=
      ((firstPrincipal H m hm*m:ℕ):ℤ) := congrArg (fun n : ℕ => (n:ℤ))
        (by simpa only [Nat.add_mul] using hqm)
  have hfi : ((firstPrincipal H m hm*m:ℕ):ℤ)=(k:ℤ)*T.g 0 := by exact_mod_cast hf
  push_cast at hfi
  have hrel : (C.exponent 0:ℤ)*T.g 0=(D.P:ℤ)*T.g 1+(D.Q:ℤ)*T.g 2 := by
    exact_mod_cast D.relationA
  constructor
  · intro j hj he
    have hsub := congrArg (fun n : ℕ => (n*T.g 2:ℕ)) (Nat.sub_add_cancel hj.le)
    have hsubi : ((D.Q-j:ℕ):ℤ)*T.g 2+(j:ℤ)*T.g 2=(D.Q:ℤ)*T.g 2 := by
      exact_mod_cast (show (D.Q-j)*T.g 2+j*T.g 2=D.Q*T.g 2 by
        simpa only [Nat.add_mul] using hsub)
    apply integer_complement_obstruction C m hm 2 hlc q (D.Q-j) hq hqQ
      (by rw [D.coherentC]; have := D.positive; omega)
      ((C.exponent 0:ℤ)-d-k)
    push_cast at hqmi ⊢
    nlinarith only [hrel,he,hqmi,hfi,hsubi]

  · intro j hj he
    have hsub := congrArg (fun n : ℕ => (n*T.g 1:ℕ)) (Nat.sub_add_cancel hj.le)
    have hsubi : ((D.P-j:ℕ):ℤ)*T.g 1+(j:ℤ)*T.g 1=(D.P:ℤ)*T.g 1 := by
      exact_mod_cast (show (D.P-j)*T.g 1+j*T.g 1=D.P*T.g 1 by
        simpa only [Nat.add_mul] using hsub)
    apply integer_complement_obstruction C m hm 1 hlb q (D.P-j) hq hqQ
      (by rw [D.coherentB]; have := D.positive; omega)
      ((C.exponent 0:ℤ)-d-k)
    push_cast at hqmi ⊢
    nlinarith only [hrel,he,hqmi,hfi,hsubi]

/-- The complete vector CT statement lands in the actual cut. The four
exponent vectors are natural, so both transported sides really belong to H. -/
theorem critical_transport_cut {H : NumericalSemigroup} (T : Triple H)
    (m n C u v : ℕ) (hn : 0<n) (hrel : C*T.g 1=u*T.g 0+v*T.g 2)
    (xi zeta xi' zeta' : Exponent) (t : ℤ)
    (hret : T.weight xi=n*m+T.weight zeta)
    (h0 : (xi' 0:ℤ)-(zeta' 0:ℤ)=(xi 0:ℤ)-(zeta 0:ℤ)-t*u)
    (h1 : (xi' 1:ℤ)-(zeta' 1:ℤ)=(xi 1:ℤ)-(zeta 1:ℤ)+t*C)
    (h2 : (xi' 2:ℤ)-(zeta' 2:ℤ)=(xi 2:ℤ)-(zeta 2:ℤ)-t*v) :
    T.weight xi'∈cyclicCut H m := by
  have hr : (C:ℤ)*T.g 1=(u:ℤ)*T.g 0+(v:ℤ)*T.g 2 := by exact_mod_cast hrel
  have hi : (xi 0:ℤ)*T.g 0+(xi 1:ℤ)*T.g 1+(xi 2:ℤ)*T.g 2=
      (n:ℤ)*m+((zeta 0:ℤ)*T.g 0+(zeta 1:ℤ)*T.g 1+(zeta 2:ℤ)*T.g 2) := by
    simp only [T.weight_three,Triple.grid] at hret
    exact_mod_cast hret
  have he := ReturnExchange.critical_transport (T.g 0:ℤ) (T.g 1:ℤ) (T.g 2:ℤ)
    C u v n m (fun i => (xi i:ℤ)) (fun i => (zeta i:ℤ))
    (fun i => (xi' i:ℤ)) (fun i => (zeta' i:ℤ)) t hr hi h0 h1 h2
  refine ⟨T.member xi',n,hn,T.weight zeta',T.member zeta',?_⟩
  simp only [T.weight_three,Triple.grid]
  exact_mod_cast he

end NS25Lean.ErasedSourceScreen
