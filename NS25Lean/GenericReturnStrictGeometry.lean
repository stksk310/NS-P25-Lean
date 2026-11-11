import NS25Lean.SharedTailPositiveChart
import NS25Lean.GenericReturnFiniteMinimum

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericReturn
open ErasedSourceScreen SharedTail PureInternalTransverse
open L5A2C4OR19
open scoped Classical

def InReturn (H : NumericalSemigroup) (nu x : ℕ) : Prop :=
  x∈H ∧ ∃ y∈H, x=nu+y

/-- Actual local predecessor conditions on the two critical components.
Positive.critical_exact_fiber identifies these with the pure and mixed
components. No return classification is an input. -/
structure LocalCut {H : NumericalSemigroup} (D : Positive H) where
  carrier : Set ℕ
  subset : ∀ x∈carrier, x∈H
  add : ∀ x∈carrier, ∀ h∈H, x+h∈carrier
  at_most_one : ∀ i j : Fin 3, j≠i →
    (D.critical.exponent i-1)*D.triple.g i∈carrier →
    D.critical.exponent i*D.triple.g i-D.triple.g j∉carrier
  center_live : ∀ j : Fin 3, D.A*D.a-D.triple.g j∉carrier

theorem critical_predecessor_mem {H : NumericalSemigroup} (D : Positive H)
    (i j : Fin 3) : D.critical.exponent i*D.triple.g i-D.triple.g j∈H := by
  have hd : D.triple.D (D.critical.exponent i*D.triple.g i) j := by
    by_cases hj : j=i
    · subst j
      simpa only [D.triple.weight_single] using
        D.triple.D_of_coordinate (Finsupp.single i (D.critical.exponent i)) i
          (by simpa using D.critical.positive i)
    · simpa only [D.witness_weight] using
        D.triple.D_of_coordinate (D.witness i) j (D.witness_positive i j hj)
  obtain ⟨r,hr,he⟩ := hd
  simpa only [he,Nat.add_sub_cancel] using hr

theorem combination_mem {H : NumericalSemigroup} (D : Positive H) (k i j : ℕ) :
    k*D.a+i*D.b+j*D.c∈H := by
  simpa only [vector_weight,Triple.grid] using D.triple.member (vector k i j)

/-- The actual nonprincipal obstruction uses only the local two-component
capacity, not a four-generator presentation or a defect hypothesis. -/
theorem no_subcritical_pure {H : NumericalSemigroup} (D : Positive H) (K : LocalCut D)
    (nu : ℕ) (hnu : 0<nu) (hnon : nu∉H)
    (hRK : ∀ x, InReturn H nu x → x∈K.carrier)
    (i : Fin 3) (n : ℕ) (hn : n<D.critical.exponent i) :
    ¬InReturn H nu (n*D.triple.g i) := by
  rintro ⟨hx,y,hy,he⟩
  have hnpos : 0<n := by
    by_contra hh
    have hz : n=0 := by omega
    simp only [hz,zero_mul] at he
    omega
  obtain ⟨e,hew⟩ := D.triple.factor y hy
  have outside_zero (j : Fin 3) (hji : j≠i) : e j=0 := by
    by_contra henz
    have hej : 0<e j := by omega
    have hpred : (D.critical.exponent i-1)*D.triple.g i∈K.carrier := by
      have hu := D.triple.member (Finsupp.single i (D.critical.exponent i-1-n))
      rw [D.triple.weight_single] at hu
      have hk := K.add _ (hRK _ ⟨hx,y,hy,he⟩) _ hu
      have hsum : n+(D.critical.exponent i-1-n)=D.critical.exponent i-1 := by omega
      simpa only [←Nat.add_mul,hsum] using hk
    have hdy := D.triple.D_of_coordinate e j hej
    rw [hew] at hdy
    obtain ⟨r,hr,hyr⟩ := hdy
    have hu := D.triple.member (Finsupp.single i (D.critical.exponent i-n))
    rw [D.triple.weight_single] at hu
    have hret : InReturn H nu (D.critical.exponent i*D.triple.g i-D.triple.g j) := by
      refine ⟨critical_predecessor_mem D i j,r+(D.critical.exponent i-n)*D.triple.g i,
        H.add_mem hr hu,?_⟩
      have hc := Nat.sub_add_cancel hn.le
      have hpos := D.triple.positive i
      change 0<D.triple.g i at hpos
      have ht : D.critical.exponent i*D.triple.g i=
          nu+(r+(D.critical.exponent i-n)*D.triple.g i)+D.triple.g j := by
        nlinarith only [he,hyr,hc]
      omega
    exact K.at_most_one i j hji hpred (hRK _ hret)
  have heq : e=Finsupp.single i (e i) := by
    ext j
    by_cases hji : j=i
    · subst j; simp
    · simp [hji,outside_zero j hji]
  rw [heq,D.triple.weight_single] at hew
  have hg := D.triple.positive i
  change 0<D.triple.g i at hg
  have hle : e i≤n := by nlinarith
  have hnueq : nu=(n-e i)*D.triple.g i := by
    have hh := Nat.sub_add_cancel hle
    nlinarith
  apply hnon
  rw [hnueq]
  simpa only [D.triple.weight_single] using D.triple.member (Finsupp.single i (n-e i))

def RB {H : NumericalSemigroup} (D : Positive H) (i j d : ℕ) : Prop :=
  D.p < i ∧ i < D.B ∧ 0 < j ∧ j < D.q ∧ 0 < d ∧ d < D.u

def LT {H : NumericalSemigroup} (D : Positive H) (i j d : ℕ) : Prop :=
  0 < i ∧ i < D.p ∧ D.q < j ∧ j < D.C ∧ 0 < d ∧ d < D.w

/-- A canonical return is forced into exactly one strict arm. -/
theorem strict_return_form {H : NumericalSemigroup} (D : Positive H) (K : LocalCut D)
    (nu i j d : ℕ) (hnu : 0<nu) (hnon : nu∉H)
    (hRK : ∀ x, InReturn H nu x → x∈K.carrier)
    (hchart : D.ChartA i j) (he : i*D.b+j*D.c=nu+d*D.a) :
    RB D i j d ∨ LT D i j d := by
  have coeff := D.coefficient_sums
  have hci := hchart.1
  have hcj := hchart.2.1
  have hcc := hchart.2.2
  have hd : 0<d := by
    by_contra h
    have hz : d=0 := by omega
    have hm := combination_mem D 0 i j
    simp only [zero_mul,zero_add] at hm
    exact hnon (by simpa only [he,hz,zero_mul,add_zero] using hm)
  have hbeta : InReturn H nu (i*D.b+j*D.c) :=
    ⟨by simpa only [zero_mul,zero_add] using combination_mem D 0 i j,
      d*D.a,by simpa only [zero_mul,add_zero] using combination_mem D d 0 0,he⟩
  have hi0 : 0 < i := by
    by_contra h
    have hz : i=0 := by omega
    have hh := no_subcritical_pure D K nu hnu hnon hRK 2 j hchart.2.1
    exact hh (by simpa only [hz,zero_mul,zero_add] using hbeta)
  have hj0 : 0<j := by
    by_contra h
    have hz : j=0 := by omega
    have hh := no_subcritical_pure D K nu hnu hnon hRK 1 i hchart.1
    exact hh (by simpa only [hz,zero_mul,add_zero] using hbeta)
  have hout : ¬(i≤D.p ∧ j≤D.q) := by
    rintro ⟨hip,hjq⟩
    rcases hchart.2.2 with hip' | hjq'
    · apply K.center_live 1
      apply hRK
      refine ⟨critical_predecessor_mem D 0 1,
        d*D.a+(D.p-i-1)*D.b+(D.q-j)*D.c,combination_mem D d _ _,?_⟩
      have hiEq : D.p-i-1+i+1=D.p := by omega
      have hjEq := Nat.sub_add_cancel hjq
      have ha := D.center
      have hba : 0<D.b := D.triple.positive 1
      have ht : D.A*D.a=nu+(d*D.a+(D.p-i-1)*D.b+(D.q-j)*D.c)+D.b := by
        nlinarith only [he,ha,hiEq,hjEq]
      change D.A*D.a-D.b=nu+(d*D.a+(D.p-i-1)*D.b+(D.q-j)*D.c)
      omega
    · apply K.center_live 2
      apply hRK
      refine ⟨critical_predecessor_mem D 0 2,
        d*D.a+(D.p-i)*D.b+(D.q-j-1)*D.c,combination_mem D d _ _,?_⟩
      have hiEq := Nat.sub_add_cancel hip
      have hjEq : D.q-j-1+j+1=D.q := by omega
      have ha := D.center
      have hca : 0<D.c := D.triple.positive 2
      have ht : D.A*D.a=nu+(d*D.a+(D.p-i)*D.b+(D.q-j-1)*D.c)+D.c := by
        nlinarith only [he,ha,hiEq,hjEq]
      change D.A*D.a-D.c=nu+(d*D.a+(D.p-i)*D.b+(D.q-j-1)*D.c)
      omega
  rcases hchart.2.2 with hip | hjq
  · right
    have hjq : D.q<j := by omega
    refine ⟨hi0,hip,hjq,hchart.2.1,hd,?_⟩
    by_contra hn
    have hwd : D.w≤d := by omega
    have hret : InReturn H nu ((D.z+i)*D.b) := by
      refine ⟨by simpa only [D.triple.weight_single] using
        D.triple.member (Finsupp.single 1 (D.z+i)),
        (d-D.w)*D.a+(D.C-j)*D.c,?_,?_⟩
      · simpa only [zero_mul,add_zero] using combination_mem D (d-D.w) 0 (D.C-j)
      · have h1 := Nat.sub_add_cancel hwd
        have h2 := Nat.sub_add_cancel hchart.2.1.le
        nlinarith only [he,D.boundary,h1,h2]
    exact no_subcritical_pure D K nu hnu hnon hRK 1 (D.z+i)
      (by change D.z+i<D.B; omega) hret
  · left
    have hip : D.p < i := by omega
    refine ⟨hip,hchart.1,hj0,hjq,hd,?_⟩
    by_contra hn
    have hud : D.u≤d := by omega
    have hret : InReturn H nu ((D.v+j)*D.c) := by
      refine ⟨by simpa only [D.triple.weight_single] using
        D.triple.member (Finsupp.single 2 (D.v+j)),
        (d-D.u)*D.a+(D.B-i)*D.b,?_,?_⟩
      · simpa only [zero_mul,add_zero] using combination_mem D (d-D.u) (D.B-i) 0
      · have h1 := Nat.sub_add_cancel hud
        have h2 := Nat.sub_add_cancel hchart.1.le
        nlinarith only [he,D.middle,h1,h2]
    exact no_subcritical_pure D K nu hnu hnon hRK 2 (D.v+j)
      (by change D.v+j<D.C; omega) hret

theorem strict_arms_disjoint {H : NumericalSemigroup} (D : Positive H) (i j d : ℕ) :
    ¬(RB D i j d ∧ LT D i j d) := by
  rintro ⟨hr,hl⟩
  have := hr.1
  have := hl.2.1
  omega

/-- Existence of the unique canonical representative is derived from the
actual chart, and nonmembership forces a strictly positive depth. -/
theorem canonical_return_exists_unique {H : NumericalSemigroup} (D : Positive H)
    (nu : ℕ) (hnon : nu∉H) :
    ∃! t : ℕ×ℕ×ℕ, D.ChartA t.1 t.2.1 ∧ 0<t.2.2 ∧
      t.1*D.b+t.2.1*D.c=nu+t.2.2*D.a := by
  obtain ⟨ij,hij,hunique⟩ := D.chart_unique_pair nu
  let i := ij.1.toNat
  let j := ij.2.toNat
  have hiZ : (i : ℤ)=ij.1 := Int.toNat_of_nonneg hij.1.1
  have hjZ : (j : ℤ)=ij.2 := Int.toNat_of_nonneg hij.1.2.1
  have hc : D.ChartA i j := by
    dsimp [Positive.ChartA]
    have sums := D.coefficient_sums
    have shape := hij.1
    rw [←hiZ,←hjZ] at shape
    dsimp [L5A2B.InLShape] at shape
    exact ⟨by exact_mod_cast (show (i : ℤ)<D.B by omega),
      by exact_mod_cast (show (j : ℤ)<D.C by omega),by
        rcases shape.2.2.2.2 with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)⟩
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hij.2
  have heZ : (i : ℤ)*D.b+j*D.c=(nu : ℤ)-(D.a : ℤ)*k := by
    rw [←hiZ,←hjZ] at hk
    linarith
  have hkneg : k<0 := by
    by_contra hh
    have hk0 : 0≤k := by omega
    have heN : nu=k.toNat*D.a+i*D.b+j*D.c := by
      exact_mod_cast (show (nu : ℤ)=(k.toNat : ℤ)*D.a+i*D.b+j*D.c by
        rw [Int.toNat_of_nonneg hk0]; nlinarith [heZ])
    exact hnon (heN ▸ combination_mem D k.toNat i j)
  let d := (-k).toNat
  have hdZ : (d : ℤ)=-k := Int.toNat_of_nonneg (by omega)
  have hd : 0<d := by omega
  have he : i*D.b+j*D.c=nu+d*D.a := by
    exact_mod_cast (show (i : ℤ)*D.b+j*D.c=(nu : ℤ)+(d : ℤ)*D.a by nlinarith [heZ,hdZ])
  refine ⟨(i,j,d),⟨hc,hd,he⟩,?_⟩
  rintro ⟨i',j',d'⟩ ⟨hc',hd',he'⟩
  obtain ⟨hic',hjc',hcorner'⟩ := hc'
  change i'<D.B at hic'
  change j'<D.C at hjc'
  change i'<D.p ∨ j'<D.q at hcorner'
  have shape' : L5A2B.InLShape D.p D.q D.z D.v i' j' := by
    dsimp [L5A2B.InLShape]
    have sums := D.coefficient_sums
    exact ⟨by positivity,by positivity,by exact_mod_cast (show i'<D.p+D.z by rw [←sums.2.1]; exact hic'),
      by exact_mod_cast (show j'<D.q+D.v by rw [←sums.2.2]; exact hjc'),by
        rcases hcorner' with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)⟩
  have mod' : Int.ModEq D.a ((i' : ℤ)*D.b+j'*D.c) nu := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(d' : ℤ),?_⟩
    have heZ' : (i' : ℤ)*D.b+j'*D.c=(nu : ℤ)+(d' : ℤ)*D.a := by exact_mod_cast he'
    nlinarith
  have hp := hunique (i',j') ⟨shape',mod'⟩
  have hi' : i'=i := by have := congrArg Prod.fst hp; dsimp at this; omega
  have hj' : j'=j := by have := congrArg Prod.snd hp; dsimp at this; omega
  have ha : 0<D.a := D.triple.positive 0
  have hd' : d'=d := by rw [hi',hj'] at he'; nlinarith
  simp only [hi',hj',hd']

theorem strict_canonical_return {H : NumericalSemigroup} (D : Positive H) (K : LocalCut D)
    (nu : ℕ) (hnu : 0<nu) (hnon : nu∉H)
    (hRK : ∀ x, InReturn H nu x → x∈K.carrier) :
    ∃! t : ℕ×ℕ×ℕ, (RB D t.1 t.2.1 t.2.2 ∨ LT D t.1 t.2.1 t.2.2) ∧
      t.1*D.b+t.2.1*D.c=nu+t.2.2*D.a := by
  obtain ⟨t,ht,hu⟩ := canonical_return_exists_unique D nu hnon
  refine ⟨t,⟨strict_return_form D K nu t.1 t.2.1 t.2.2 hnu hnon hRK ht.1 ht.2.2,ht.2.2⟩,?_⟩
  intro s hs
  apply hu
  refine ⟨?_,?_,hs.2⟩
  · rcases hs.1 with hr | hl
    · obtain ⟨hpi,hiB,hj0,hjq,hd0,hdu⟩ := hr
      exact ⟨hiB,by have sums := D.coefficient_sums; omega,Or.inr hjq⟩
    · obtain ⟨hi0,hip,hqj,hjC,hd0,hdw⟩ := hl
      exact ⟨by have sums := D.coefficient_sums; omega,hjC,Or.inl hip⟩
  · rcases hs.1 with hr | hl
    · exact hr.2.2.2.2.1
    · exact hl.2.2.2.2.1

end NS25Lean.GenericReturn
