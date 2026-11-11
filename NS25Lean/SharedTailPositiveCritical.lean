import NS25Lean.SharedTailModePresentation

set_option autoImplicit false
set_option linter.style.header false
set_option maxHeartbeats 1200000
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse CriticalCapGeometry CriticalPresentationModes L3C

/-- Exactly the standalone positive critical-presentation hypotheses.
All critical exponents are true minima. No coherence, chart, ideal, or
lattice-basis conclusion is a field. -/
structure Positive (H : NumericalSemigroup) where
  triple : Triple H
  critical : Critical triple
  p : ℕ
  q : ℕ
  u : ℕ
  v : ℕ
  w : ℕ
  z : ℕ
  p_pos : 0<p
  q_pos : 0<q
  u_pos : 0<u
  v_pos : 0<v
  w_pos : 0<w
  z_pos : 0<z
  center : critical.exponent 0*triple.g 0=p*triple.g 1+q*triple.g 2
  middle : critical.exponent 1*triple.g 1=u*triple.g 0+v*triple.g 2
  boundary : critical.exponent 2*triple.g 2=w*triple.g 0+z*triple.g 1
  primitive : Nat.gcd (triple.g 0) (Nat.gcd (triple.g 1) (triple.g 2))=1

abbrev Positive.a {H : NumericalSemigroup} (D : Positive H) := D.triple.g 0
abbrev Positive.b {H : NumericalSemigroup} (D : Positive H) := D.triple.g 1
abbrev Positive.c {H : NumericalSemigroup} (D : Positive H) := D.triple.g 2
abbrev Positive.A {H : NumericalSemigroup} (D : Positive H) := D.critical.exponent 0
abbrev Positive.B {H : NumericalSemigroup} (D : Positive H) := D.critical.exponent 1
abbrev Positive.C {H : NumericalSemigroup} (D : Positive H) := D.critical.exponent 2

def Positive.witness {H : NumericalSemigroup} (D : Positive H) : Fin 3→Exponent
  | 0 => vector 0 D.p D.q
  | 1 => vector D.u 0 D.v
  | 2 => vector D.w D.z 0

theorem Positive.witness_zero {H : NumericalSemigroup} (D : Positive H) (i : Fin 3) :
    D.witness i i=0 := by fin_cases i <;> simp [Positive.witness]

theorem Positive.witness_positive {H : NumericalSemigroup} (D : Positive H)
    (i j : Fin 3) (hij : j≠i) : 0<D.witness i j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [Positive.witness,D.p_pos,D.q_pos,D.u_pos,D.v_pos,D.w_pos,D.z_pos]

theorem Positive.witness_weight {H : NumericalSemigroup} (D : Positive H) (i : Fin 3) :
    D.triple.weight (D.witness i)=D.critical.exponent i*D.triple.g i := by
  fin_cases i <;> simp only [Positive.witness,vector_weight,Triple.grid,
    zero_mul,zero_add,add_zero]
  · exact D.center.symm
  · exact D.middle.symm
  · exact D.boundary.symm

theorem critical_pure_unique {H : NumericalSemigroup} (T : Triple H) (C : Critical T)
    (i : Fin 3) (e : Exponent) (he : T.weight e=C.exponent i*T.g i) (hi : 0<e i) :
    e=Finsupp.single i (C.exponent i) := by
  have hs := T.weight_split e i
  have hp := T.positive i
  change 0<T.g i at hp
  have hle : e i≤C.exponent i := by nlinarith
  have hnot : ¬e i<C.exponent i := by
    intro hlt
    have hh := congrArg (fun n => n*T.g i) (Nat.sub_add_cancel hle)
    simp only [Nat.add_mul] at hh
    have hm := C.least i (C.exponent i-e i) (e.erase i) (by omega) (by simp)
      (by nlinarith : (C.exponent i-e i)*T.g i=T.weight (e.erase i))
    omega
  have heq : e i=C.exponent i := by omega
  have hz : T.weight (e.erase i)=0 := by nlinarith
  have her := T.weight_eq_zero hz
  have hrec := Finsupp.single_add_erase i e
  simpa [heq,her] using hrec.symm

theorem Positive.cross_bound {H : NumericalSemigroup} (D : Positive H)
    (i j : Fin 3) (hij : i≠j) : D.witness i j<D.critical.exponent j := by
  classical
  obtain ⟨k,hki,hkj⟩ : ∃ k : Fin 3, k≠i ∧ k≠j := by
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first | exact ⟨0,by decide,by decide⟩ | exact ⟨1,by decide,by decide⟩ |
        exact ⟨2,by decide,by decide⟩
  by_contra hn
  have hle : Finsupp.single j (D.critical.exponent j)≤D.witness i :=
    Finsupp.single_le_iff.mpr (by omega)
  let e := D.witness i-Finsupp.single j (D.critical.exponent j)+D.witness j
  have hew : D.triple.weight e=D.critical.exponent i*D.triple.g i := by
    have hh := congrArg D.triple.weight (tsub_add_cancel_of_le hle)
    rw [map_add,D.triple.weight_single,D.witness_weight] at hh
    dsimp [e]
    rw [map_add,D.witness_weight]
    omega
  have hei : 0<e i := by
    have hp := D.witness_positive j i hij
    dsimp [e]
    simp only [Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_eq_of_ne hij]
    omega
  have hek : 0<e k := by
    have hp := D.witness_positive i k hki
    dsimp [e]
    simp only [Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_eq_of_ne hkj]
    omega
  have he := critical_pure_unique D.triple D.critical i e hew hei
  rw [he,Finsupp.single_eq_of_ne hki] at hek
  omega

theorem Positive.strict_bounds {H : NumericalSemigroup} (D : Positive H) :
    D.p<D.B ∧ D.q<D.C ∧ D.u<D.A ∧ D.v<D.C ∧ D.w<D.A ∧ D.z<D.B := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [Positive.witness,vector_one] using D.cross_bound 0 1 (by decide)
  · simpa only [Positive.witness,vector_two] using D.cross_bound 0 2 (by decide)
  · simpa only [Positive.witness,vector_zero] using D.cross_bound 1 0 (by decide)
  · simpa only [Positive.witness,vector_two] using D.cross_bound 1 2 (by decide)
  · simpa only [Positive.witness,vector_zero] using D.cross_bound 2 0 (by decide)
  · simpa only [Positive.witness,vector_one] using D.cross_bound 2 1 (by decide)

theorem Positive.coefficient_sums {H : NumericalSemigroup} (D : Positive H) :
    D.A=D.u+D.w ∧ D.B=D.p+D.z ∧ D.C=D.q+D.v := by
  have hb := D.strict_bounds
  have hA : D.A≤D.u+D.w := by
    apply D.critical.least 0 (D.u+D.w) (vector 0 (D.B-D.z) (D.C-D.v))
      (by have := D.u_pos; omega) (by simp)
    rw [vector_weight,Triple.grid]
    have h1 := Nat.sub_add_cancel hb.2.2.2.2.2.le
    have h2 := Nat.sub_add_cancel hb.2.2.2.1.le
    nlinarith [D.middle,D.boundary]
  have hB : D.B≤D.p+D.z := by
    apply D.critical.least 1 (D.p+D.z) (vector (D.A-D.w) 0 (D.C-D.q))
      (by have := D.p_pos; omega) (by simp)
    rw [vector_weight,Triple.grid]
    have h1 := Nat.sub_add_cancel hb.2.2.2.2.1.le
    have h2 := Nat.sub_add_cancel hb.2.1.le
    nlinarith [D.center,D.boundary]
  have hC : D.C≤D.q+D.v := by
    apply D.critical.least 2 (D.q+D.v) (vector (D.A-D.u) (D.B-D.p) 0)
      (by have := D.q_pos; omega) (by simp)
    rw [vector_weight,Triple.grid]
    have h1 := Nat.sub_add_cancel hb.2.2.1.le
    have h2 := Nat.sub_add_cancel hb.1.le
    nlinarith [D.center,D.middle]
  have ha := D.triple.positive 0
  have hb := D.triple.positive 1
  have hc := D.triple.positive 2
  change 0<D.a at ha
  change 0<D.b at hb
  change 0<D.c at hc
  constructor
  · nlinarith [D.center,D.middle,D.boundary]
  constructor <;> nlinarith [D.center,D.middle,D.boundary]

def Positive.toBase {H : NumericalSemigroup} (D : Positive H) (m : ℕ) (hm : 0<m) : Base H where
  triple := D.triple
  critical := D.critical
  m := m
  m_pos := hm
  u := D.u
  v := D.v
  u_pos := D.u_pos
  v_pos := D.v_pos
  tie := D.middle

def Positive.toMode {H : NumericalSemigroup} (D : Positive H) (m : ℕ) (hm : 0<m) :
    Mode (D.toBase m hm) :=
  .positive D.p D.q D.w D.z D.p_pos D.q_pos D.w_pos D.z_pos
    D.coefficient_sums.1 D.coefficient_sums.2.1 D.coefficient_sums.2.2 D.center D.boundary

theorem weight_axes {H : NumericalSemigroup} (T : Triple H) (i j k : Fin 3)
    (hij : i≠j) (hki : k≠i) (hkj : k≠j) (e : Exponent) :
    T.weight e=e i*T.g i+e j*T.g j+e k*T.g k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [T.weight_three,Triple.grid] <;> omega

/-- An outside factorization below both opposite critical thresholds is unique.
The proof uses actual least outside exponents, not a lattice-rank assumption. -/
theorem outside_unique {H : NumericalSemigroup} (T : Triple H) (C : Critical T)
    (i j k : Fin 3) (hij : i≠j) (hki : k≠i) (hkj : k≠j)
    (e r : Exponent) (hei : e i=0) (hri : r i=0)
    (hrj : r j<C.exponent j) (hrk : r k<C.exponent k)
    (he : T.weight e=T.weight r) : e=r := by
  have hew := weight_axes T i j k hij hki hkj e
  have hrw := weight_axes T i j k hij hki hkj r
  rw [hei,zero_mul,zero_add] at hew
  rw [hri,zero_mul,zero_add] at hrw
  have hjp := T.positive j
  have hkp := T.positive k
  change 0<T.g j at hjp
  change 0<T.g k at hkp
  have heqj : e j=r j := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hk : r k<e k := by nlinarith
      have hhj := Nat.sub_add_cancel hlt.le
      have hhk := Nat.sub_add_cancel hk.le
      have hm := C.least j (r j-e j) (Finsupp.single k (e k-r k))
        (by omega) (by simp [Ne.symm hkj]) (by
          rw [T.weight_single]
          nlinarith)
      omega
    · have hk : e k<r k := by nlinarith
      have hhj := Nat.sub_add_cancel hgt.le
      have hhk := Nat.sub_add_cancel hk.le
      have hm := C.least k (r k-e k) (Finsupp.single j (e j-r j))
        (by omega) (by simp [hkj]) (by
          rw [T.weight_single]
          nlinarith)
      omega
  have heqk : e k=r k := by nlinarith
  ext l
  have hl : l=i ∨ l=j ∨ l=k := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
  rcases hl with rfl | rfl | rfl
  · exact hei.trans hri.symm
  · exact heqj
  · exact heqk

/-- Every positive critical fiber has exactly its displayed pure and mixed
factorizations. The witness is the actual given positive mixed factorization. -/
theorem Positive.critical_exact_fiber {H : NumericalSemigroup} (D : Positive H)
    (i : Fin 3) (e : Exponent)
    (he : D.triple.weight e=D.critical.exponent i*D.triple.g i) :
    e=Finsupp.single i (D.critical.exponent i) ∨ e=D.witness i := by
  by_cases hi : e i=0
  · right
    obtain ⟨j,k,hij,hki,hkj⟩ : ∃ j k : Fin 3, i≠j ∧ k≠i ∧ k≠j := by
      fin_cases i
      · exact ⟨1,2,by decide,by decide,by decide⟩
      · exact ⟨0,2,by decide,by decide,by decide⟩
      · exact ⟨0,1,by decide,by decide,by decide⟩
    exact outside_unique D.triple D.critical i j k hij hki hkj e (D.witness i)
      hi (D.witness_zero i) (D.cross_bound i j hij) (D.cross_bound i k hki.symm)
      (he.trans (D.witness_weight i).symm)
  · exact Or.inl (critical_pure_unique D.triple D.critical i e he (Nat.pos_of_ne_zero hi))

theorem Positive.critical_degrees_distinct {H : NumericalSemigroup} (D : Positive H)
    (i j : Fin 3) (hij : i≠j) :
    D.critical.exponent i*D.triple.g i≠D.critical.exponent j*D.triple.g j := by
  intro he
  have hf := D.critical_exact_fiber i (Finsupp.single j (D.critical.exponent j))
    (by rw [D.triple.weight_single]; exact he.symm)
  rcases hf with hf | hf
  · have hc := congrArg (fun e : Exponent => e j) hf
    simp [Ne.symm hij] at hc
    have := D.critical.positive j
    omega
  · obtain ⟨k,hki,hkj⟩ : ∃ k : Fin 3, k≠i ∧ k≠j := by
      fin_cases i <;> fin_cases j <;> simp_all <;>
        first | exact ⟨0,by decide,by decide⟩ | exact ⟨1,by decide,by decide⟩ |
          exact ⟨2,by decide,by decide⟩
    have hc := congrArg (fun e : Exponent => e k) hf
    have hp := D.witness_positive i k hki
    simp [hkj] at hc
    omega

end NS25Lean.SharedTail
