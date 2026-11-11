import NS25Lean.SharedTailPositiveCritical
import NS25Lean.GenericLShapeCompleteness
set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse CriticalCapGeometry CriticalPresentationModes L3C
open L5A2B GenericLShape
private theorem unique_zero_nat
    (a b c c1 c2 c3 p q v z : ℕ)
    (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hp : 0 < p) (hq : 0 < q) (_hv : 0 < v) (_hz : 0 < z)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hrel1 : c1 * a = p * b + q * c)
    (hmin1 : ∀ n x y : ℕ, 0 < n → n * a = x * b + y * c → c1 ≤ n)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n)
    {i j k : ℕ} (hi : i < p + z) (hj : j < q + v)
    (hcorner : i < p ∨ j < q) (hzero : i * b + j * c = k * a) :
    i = 0 ∧ j = 0 := by
  by_cases hk0 : k = 0
  · subst k
    constructor <;> nlinarith
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hc1k : c1 ≤ k := hmin1 k i j hk hzero.symm
  rcases hcorner with hip | hjq
  · have hqj : q < j := by
      by_contra hn
      have hjle : j ≤ q := by omega
      nlinarith only [hzero, hrel1, hip, hjle, hb, hc, hc1k, _ha]
    have hsubk : k - c1 + c1 = k := Nat.sub_add_cancel hc1k
    have hsubi : p - i + i = p := Nat.sub_add_cancel (le_of_lt hip)
    have hsubj : j - q + q = j := Nat.sub_add_cancel (le_of_lt hqj)
    have hrel : (j - q) * c = (k - c1) * a + (p - i) * b := by
      nlinarith only [hzero, hrel1, hsubk, hsubi, hsubj]
    have hmin := hmin3 (j - q) (k - c1) (p - i) (Nat.sub_pos_of_lt hqj) hrel
    omega
  · have hpi : p < i := by
      by_contra hn
      have hile : i ≤ p := by omega
      nlinarith only [hzero, hrel1, hjq, hile, hb, hc, hc1k, _ha]
    have hsubk : k - c1 + c1 = k := Nat.sub_add_cancel hc1k
    have hsubi : i - p + p = i := Nat.sub_add_cancel (le_of_lt hpi)
    have hsubj : q - j + j = q := Nat.sub_add_cancel (le_of_lt hjq)
    have hrel : (i - p) * b = (k - c1) * a + (q - j) * c := by
      nlinarith only [hzero, hrel1, hsubk, hsubi, hsubj]
    have hmin := hmin2 (i - p) (k - c1) (q - j) (Nat.sub_pos_of_lt hpi) hrel
    omega

private theorem uniqueZeroInLShape_of_nat
    (a b c c1 c2 c3 p q v z : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hp : 0 < p) (hq : 0 < q) (hv : 0 < v) (hz : 0 < z)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hrel1 : c1 * a = p * b + q * c)
    (hmin1 : ∀ n x y : ℕ, 0 < n → n * a = x * b + y * c → c1 ≤ n)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n) :
    UniqueZeroInLShape (a : ℤ) (b : ℤ) (c : ℤ)
      (p : ℤ) (q : ℤ) (z : ℤ) (v : ℤ) := by
  intro i j hshape hzero
  rcases hshape with ⟨hi0, hj0, hi, hj, hcorner⟩
  rcases hzero with ⟨k, hk⟩
  have hk0 : 0 ≤ k := by nlinarith
  let ni := i.toNat
  let nj := j.toNat
  let nk := k.toNat
  have hii : (ni : ℤ) = i := Int.toNat_of_nonneg hi0
  have hjj : (nj : ℤ) = j := Int.toNat_of_nonneg hj0
  have hkk : (nk : ℤ) = k := Int.toNat_of_nonneg hk0
  have hni : ni < p + z := by rw [← hii] at hi; exact_mod_cast hi
  have hnj : nj < q + v := by rw [← hjj] at hj; exact_mod_cast hj
  have hncorner : ni < p ∨ nj < q := by
    rcases hcorner with h | h
    · rw [← hii] at h; exact Or.inl (by exact_mod_cast h)
    · rw [← hjj] at h; exact Or.inr (by exact_mod_cast h)
  have hnzero : ni * b + nj * c = nk * a := by
    rw [← hii, ← hjj, ← hkk] at hk
    exact_mod_cast hk
  obtain ⟨hni0, hnj0⟩ := unique_zero_nat a b c c1 c2 c3 p q v z
    ha hb hc hp hq hv hz hs2 hs3 hrel1 hmin1 hmin2 hmin3 hni hnj hncorner hnzero
  constructor
  · rw [← hii]; exact_mod_cast hni0
  · rw [← hjj]; exact_mod_cast hnj0


theorem Positive.least_a {H : NumericalSemigroup} (D : Positive H)
    (n x y : ℕ) (hn : 0<n) (he : n*D.a=x*D.b+y*D.c) : D.A≤n :=
  D.critical.least 0 n (vector 0 x y) hn (by simp)
    (by simpa [vector_weight,Triple.grid] using he)

theorem Positive.least_b {H : NumericalSemigroup} (D : Positive H)
    (n x y : ℕ) (hn : 0<n) (he : n*D.b=x*D.a+y*D.c) : D.B≤n :=
  D.critical.least 1 n (vector x 0 y) hn (by simp)
    (by simpa [vector_weight,Triple.grid] using he)

theorem Positive.least_c {H : NumericalSemigroup} (D : Positive H)
    (n x y : ℕ) (hn : 0<n) (he : n*D.c=x*D.a+y*D.b) : D.C≤n :=
  D.critical.least 2 n (vector x y 0) hn (by simp)
    (by simpa [vector_weight,Triple.grid] using he)

def Positive.ChartA {H : NumericalSemigroup} (D : Positive H) (i j : ℕ) : Prop :=
  i<D.B ∧ j<D.C ∧ (i<D.p ∨ j<D.q)
def Positive.ChartB {H : NumericalSemigroup} (D : Positive H) (i j : ℕ) : Prop :=
  i<D.A ∧ j<D.C ∧ (i<D.u ∨ j<D.v)
def Positive.ChartC {H : NumericalSemigroup} (D : Positive H) (i j : ℕ) : Prop :=
  i<D.A ∧ j<D.B ∧ (i<D.w ∨ j<D.z)

theorem Positive.unique_zero {H : NumericalSemigroup} (D : Positive H) :
    UniqueZeroInLShape D.a D.b D.c D.p D.q D.z D.v := by
  apply uniqueZeroInLShape_of_nat D.a D.b D.c D.A D.B D.C D.p D.q D.v D.z
  · exact D.triple.positive 0
  · exact D.triple.positive 1
  · exact D.triple.positive 2
  · exact D.p_pos
  · exact D.q_pos
  · exact D.v_pos
  · exact D.z_pos
  · exact D.coefficient_sums.2.1
  · exact D.coefficient_sums.2.2
  · exact D.center
  · exact D.least_a
  · exact D.least_b
  · exact D.least_c

theorem Positive.residue_bijective {H : NumericalSemigroup} (D : Positive H) :
    Function.Bijective (GenericLShape.residue D.a D.b D.c D.p D.q D.z D.v) :=
  GenericLShape.residue_bijective D.a D.b D.c D.A D.B D.C D.p D.q D.z D.v D.u D.w
    (D.triple.positive 0) D.p_pos D.q_pos D.z_pos D.v_pos
    D.coefficient_sums.2.1 D.coefficient_sums.2.2 D.center D.middle D.boundary
    D.least_b D.least_c D.unique_zero D.primitive

theorem Positive.chart_unique_pair {H : NumericalSemigroup} (D : Positive H) (n : ℤ) :
    ∃! ij : ℤ×ℤ, InLShape D.p D.q D.z D.v ij.1 ij.2 ∧
      Int.ModEq D.a (ij.1*D.b+ij.2*D.c) n :=
  GenericLShape.existsUnique_pair D.a D.b D.c D.A D.B D.C D.p D.q D.z D.v D.u D.w
    (D.triple.positive 0) D.p_pos D.q_pos D.z_pos D.v_pos
    D.coefficient_sums.2.1 D.coefficient_sums.2.2 D.center D.middle D.boundary
    D.least_b D.least_c D.unique_zero D.primitive n

/-- Arbitrary factorizations of an omitted-axis canonical point are unique;
there is no chart restriction on the competing factorization. -/
theorem Positive.chartA_factorization_unique {H : NumericalSemigroup} (D : Positive H)
    (i j : ℕ) (hc : D.ChartA i j) (e : Exponent)
    (he : D.triple.weight e=i*D.b+j*D.c) : e=vector 0 i j := by
  apply (D.toMode 1 (by decide)).short_yz (mode_genuine _) i j hc.1 hc.2.1 hc.2.2 e
  simpa [Positive.toBase,vector_weight,Triple.grid] using he

theorem Positive.chartB_factorization_unique {H : NumericalSemigroup} (D : Positive H)
    (i j : ℕ) (hc : D.ChartB i j) (e : Exponent)
    (he : D.triple.weight e=i*D.a+j*D.c) : e=vector i 0 j := by
  apply (D.toMode 1 (by decide)).short_xz (mode_genuine _) i j hc.1 hc.2.1 hc.2.2 e
  simpa [Positive.toBase,vector_weight,Triple.grid] using he

theorem Positive.chartC_factorization_unique {H : NumericalSemigroup} (D : Positive H)
    (i j : ℕ) (hc : D.ChartC i j) (e : Exponent)
    (he : D.triple.weight e=i*D.a+j*D.b) : e=vector i j 0 := by
  apply (D.toMode 1 (by decide)).short_xy (mode_genuine _) i j hc.1 hc.2.1 hc.2.2 e
  simpa [Positive.toBase,vector_weight,Triple.grid] using he

theorem Positive.chartA_apery {H : NumericalSemigroup} (D : Positive H)
    (i j : ℕ) (hc : D.ChartA i j) : i*D.b+j*D.c∈FourGeneratedBridge.aperySet H.toAddSubmonoid D.a := by
  have hm : i*D.b+j*D.c∈H := by
    simpa [vector_weight,Triple.grid] using D.triple.member (vector 0 i j)
  refine ⟨hm,?_⟩
  by_cases hlt : i*D.b+j*D.c<D.a
  · exact Or.inl hlt
  · right
    intro hk
    obtain ⟨e,he⟩ := D.triple.factor _ hk
    have hw : D.triple.weight (Finsupp.single 0 1+e)=i*D.b+j*D.c := by
      rw [map_add,D.triple.weight_single,one_mul,he]
      change D.a+(i*D.b+j*D.c-D.a)=i*D.b+j*D.c
      omega
    have hu := D.chartA_factorization_unique i j hc _ hw
    have hi := congrArg (fun v : Exponent => v 0) hu
    simp at hi

theorem Positive.chartA_failure_of_positive_a {H : NumericalSemigroup} (D : Positive H)
    (i j s : ℕ) (hs : 0<s) (e : Exponent)
    (he : i*D.b+j*D.c=s*D.a+D.triple.weight e) :
    D.B ≤ i ∨ D.C ≤ j ∨ (D.p ≤ i ∧ D.q ≤ j) := by
  by_contra hn
  have hc : D.ChartA i j := by dsimp [Positive.ChartA]; omega
  have hw : D.triple.weight (Finsupp.single 0 s+e)=i*D.b+j*D.c := by
    rw [map_add,D.triple.weight_single]; exact he.symm
  have hu := D.chartA_factorization_unique i j hc _ hw
  have hi := congrArg (fun v : Exponent => v 0) hu
  simp only [Finsupp.add_apply,Finsupp.single_eq_same,vector_zero] at hi
  omega

theorem Positive.chartA_reduction {H : NumericalSemigroup} (D : Positive H) (x y : ℕ) :
    ∃ i j s : ℕ, D.ChartA i j ∧ x*D.b+y*D.c=i*D.b+j*D.c+s*D.a :=
  GenericLShape.exists_reduction D.a D.b D.c D.A D.B D.C D.p D.q D.z D.v D.u D.w
    (D.triple.positive 0) (D.critical.positive 0) D.u_pos D.w_pos
    D.coefficient_sums.2.1 D.coefficient_sums.2.2 D.center D.middle D.boundary x y

theorem Positive.normal_form_exists {H : NumericalSemigroup} (D : Positive H)
    (h : ℕ) (hh : h∈H) : ∃ s i j : ℕ, D.ChartA i j ∧ h=s*D.a+i*D.b+j*D.c := by
  obtain ⟨e,he⟩ := D.triple.factor h hh
  obtain ⟨i,j,s,hc,hs⟩ := D.chartA_reduction (e 1) (e 2)
  refine ⟨e 0+s,i,j,hc,?_⟩
  have hw := D.triple.weight_three e
  dsimp [Triple.grid] at hw
  nlinarith

end NS25Lean.SharedTail
