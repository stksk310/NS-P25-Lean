import NS25Lean.GenericReturnStrictGeometry

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericReturn
open SharedTail ErasedSourceScreen PureInternalTransverse
open L5A2B4AR1 L5A2C4H L5A2C4OR3
open scoped Classical
variable {H : NumericalSemigroup}

theorem relations_int (D : Positive H) :
    (D.A : ℤ)*D.a=(D.p : ℤ)*D.b+D.q*D.c ∧
    (D.B : ℤ)*D.b=(D.u : ℤ)*D.a+D.v*D.c ∧
    (D.C : ℤ)*D.c=(D.w : ℤ)*D.a+D.z*D.b :=
  ⟨by exact_mod_cast D.center,by exact_mod_cast D.middle,by exact_mod_cast D.boundary⟩

theorem combination_int (D : Positive H) (k i j : ℤ)
    (hk : 0 ≤ k) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    k*D.a+i*D.b+j*D.c∈H.asRelativeIdeal := by
  refine ⟨k.toNat*D.a+i.toNat*D.b+j.toNat*D.c,combination_mem D _ _ _,?_⟩
  simp [Int.toNat_of_nonneg hk,Int.toNat_of_nonneg hi,Int.toNat_of_nonneg hj]

theorem factorization_int (D : Positive H) (x : ℤ) (hx : x∈H.asRelativeIdeal) :
    ∃ k i j : ℕ, x=(k : ℤ)*D.a+i*D.b+j*D.c := by
  obtain ⟨n,hn,he⟩ := hx
  obtain ⟨e,hew⟩ := D.triple.factor n hn
  have hs := D.triple.weight_three e
  dsimp [Triple.grid] at hs
  exact ⟨e 0,e 1,e 2,by rw [he,←hew,hs]; push_cast; rfl⟩

theorem ideal_add_int (I : RelativeIdeal H) {x y : ℤ}
    (hx : x∈I) (hy : y∈H.asRelativeIdeal) : x+y∈I := by
  obtain ⟨n,hn,he⟩ := hy
  rw [he]
  exact I.add_mem hx hn

theorem canonical_not_positive_a (D : Positive H) (i j : ℕ)
    (hi : i<D.B) (hj : j<D.C) (hc : i<D.p ∨ j<D.q)
    (k : ℤ) (hk : 0<k) (y : ℤ) (hy : y∈H.asRelativeIdeal) :
    (i : ℤ)*D.b+j*D.c≠k*D.a+y := by
  intro he
  obtain ⟨r,hr,hry⟩ := hy
  obtain ⟨e,hew⟩ := D.triple.factor r hr
  have hk0 : 0≤k := by omega
  have heN : i*D.b+j*D.c=k.toNat*D.a+D.triple.weight e := by
    rw [hew]
    exact_mod_cast (show (i : ℤ)*D.b+j*D.c=(k.toNat : ℤ)*D.a+r by
      rw [Int.toNat_of_nonneg hk0]; omega)
  have hf := D.chartA_failure_of_positive_a i j k.toNat
    (by omega) e heN
  rcases hf with hf | hf | ⟨hf,hg⟩ <;> omega

theorem return_rectangle_cover (D : Positive H)
    (n i j d ib jb : ℕ)
    (he : (i : ℤ) * D.b + j * D.c =
      n + d * D.a)
    (hrect : ∀ u v : ℕ, u < ib → v < jb →
      u < D.B ∧ v < D.C ∧
      (u < D.p ∨ v < D.q))
    (hA : (i : ℤ) * D.b + jb * D.c - d * D.a ∈
      returnIdeal (H) n)
    (hB : (ib : ℤ) * D.b + j * D.c - d * D.a ∈
      returnIdeal (H) n)
    (x : ℤ) :
    x ∈ returnIdeal (H) n ↔
    x - ((i : ℤ) * D.b + j * D.c) ∈ (H).asRelativeIdeal ∨
    x - ((i : ℤ) * D.b + jb * D.c - d * D.a) ∈ (H).asRelativeIdeal ∨
    x - ((ib : ℤ) * D.b + j * D.c - d * D.a) ∈ (H).asRelativeIdeal := by
  have hbeta : (i : ℤ) * D.b + j * D.c ∈
      returnIdeal (H) n := by
    rw [mem_returnIdeal_iff]
    refine ⟨?_, ?_⟩
    · simpa using combination_int D 0 i j le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [he]
      convert combination_int D d 0 0 (Nat.cast_nonneg _) le_rfl le_rfl using 1 <;> ring
  constructor
  · intro hx
    obtain ⟨A, B, C, hf⟩ := factorization_int D _ hx.2
    have heq : x + (d : ℤ) * D.a =
        (i : ℤ) * D.b + j * D.c +
        (A : ℤ) * D.a + B * D.b + C * D.c := by
      linarith
    by_cases hAd : d ≤ A
    · left
      convert combination_int D ((A : ℤ)-d) B C (by omega) (Nat.cast_nonneg _) (Nat.cast_nonneg _) using 1 <;> nlinarith only [heq]
    · by_cases hbi : i + B < ib
      · by_cases hcj : j + C < jb
        · obtain ⟨hi, hj, hc⟩ := hrect _ _ hbi hcj
          exfalso
          apply canonical_not_positive_a D (i+B) (j+C) hi hj hc ((d : ℤ)-A) (by omega) x hx.1
          simp only [Nat.cast_add]
          nlinarith only [heq]
        · right; left
          convert combination_int D A B ((j : ℤ)+C-jb) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by omega) using 1 <;> nlinarith only [heq]
      · right; right
        convert combination_int D A ((i : ℤ)+B-ib) C (Nat.cast_nonneg _) (by omega) (Nat.cast_nonneg _) using 1 <;> nlinarith only [heq]
  · intro hx
    rcases hx with hx | hx | hx
    · have hm := ideal_add_int (returnIdeal (H) n) hbeta hx
      convert hm using 1 <;> ring
    · have hm := ideal_add_int (returnIdeal (H) n) hA hx
      convert hm using 1 <;> ring
    · have hm := ideal_add_int (returnIdeal (H) n) hB hx
      convert hm using 1 <;> ring


theorem boundary_mem (D : Positive H)
    (n i j d ib jb : ℕ) (hij : i ≤ ib) (hjj : j ≤ jb)
    (he : (i : ℤ)*D.b+j*D.c = n+d*D.a)
    (hmem : (ib : ℤ)*D.b+jb*D.c-d*D.a ∈ (H).asRelativeIdeal) :
    (ib : ℤ)*D.b+jb*D.c-d*D.a ∈ returnIdeal (H) n := by
  refine ⟨hmem, ?_⟩
  change (ib : ℤ)*D.b+jb*D.c-d*D.a-n ∈ (H).asRelativeIdeal
  convert combination_int D 0 ((ib : ℤ)-i) ((jb : ℤ)-j)
    le_rfl (by omega) (by omega) using 1 <;> nlinarith only [he]

def ltAxisA (D : Positive H) (i j d : ℕ) : ℤ :=
  ((D.w : ℤ)-d)*D.a + ((i : ℤ)+D.z)*D.b + (0)*D.c

def ltAxisB (D : Positive H) (i j d : ℕ) : ℤ :=
  ((D.A : ℤ)-d)*D.a + (0)*D.b + ((j : ℤ)-D.q)*D.c

theorem lt_axes_mem (D : Positive H)
    (n i j d : ℕ) (hi0 : 0 < i) (hj0 : 0 < j) (hd0 : 0 < d)
    (hi : i < D.p)
    (hj : D.q < j)
    (hib : i < D.B) (hjb : j < D.C)
    (hd : d < D.w)
    (he : (i : ℤ)*D.b+j*D.c =
      n+d*D.a) :
    ltAxisA D i j d ∈ returnIdeal (H) n ∧
    ltAxisB D i j d ∈ returnIdeal (H) n := by
  have hr := relations_int D
  have hs := D.coefficient_sums
  have hdC : d ≤ D.A := by omega
  have hAeq : ltAxisA D i j d =
      (i : ℤ)*D.b+(D.C : ℤ)*D.c-d*D.a := by
    unfold ltAxisA
    nlinarith only [hr.2.2]
  have hBeq : ltAxisB D i j d =
      (D.p : ℤ)*D.b+(j : ℤ)*D.c-d*D.a := by
    unfold ltAxisB
    nlinarith only [hr.1]
  constructor
  · rw [hAeq]
    apply boundary_mem D n i j d i (D.C) le_rfl (by omega) he
    rw [← hAeq]
    unfold ltAxisA
    apply combination_int D <;> omega
  · rw [hBeq]
    apply boundary_mem D n i j d (D.p) j (by omega) le_rfl he
    rw [← hBeq]
    unfold ltAxisB
    apply combination_int D <;> omega

theorem lt_return_three_generators (D : Positive H)
    (n i j d : ℕ) (hi0 : 0 < i) (hj0 : 0 < j) (hd0 : 0 < d)
    (hi : i < D.p)
    (hj : D.q < j)
    (hib : i < D.B) (hjb : j < D.C)
    (hd : d < D.w)
    (he : (i : ℤ)*D.b+j*D.c =
      n+d*D.a) (x : ℤ) :
    x ∈ returnIdeal (H) n ↔
    x-((i : ℤ)*D.b+j*D.c) ∈ (H).asRelativeIdeal ∨
    x-ltAxisA D i j d ∈ (H).asRelativeIdeal ∨
    x-ltAxisB D i j d ∈ (H).asRelativeIdeal := by
  have hr := relations_int D
  have hs := D.coefficient_sums
  have ha := lt_axes_mem D n i j d hi0 hj0 hd0 hi hj hib hjb hd he
  have hAeq : ltAxisA D i j d =
      (i : ℤ)*D.b+(D.C : ℤ)*D.c-d*D.a := by
    unfold ltAxisA
    nlinarith only [hr.2.2]
  have hBeq : ltAxisB D i j d =
      (D.p : ℤ)*D.b+(j : ℤ)*D.c-d*D.a := by
    unfold ltAxisB
    nlinarith only [hr.1]
  rw [hAeq, hBeq] at ha ⊢
  exact return_rectangle_cover D n i j d (D.p) (D.C) he
    (by intro u v hu hv; exact ⟨by omega, by omega, Or.inl hu⟩) ha.1 ha.2 x

def rbAxisA (D : Positive H) (i j d : ℕ) : ℤ :=
  ((D.A : ℤ)-d)*D.a + ((i : ℤ)-D.p)*D.b + (0)*D.c

def rbAxisB (D : Positive H) (i j d : ℕ) : ℤ :=
  ((D.u : ℤ)-d)*D.a + (0)*D.b + ((j : ℤ)+D.v)*D.c

theorem rb_axes_mem (D : Positive H)
    (n i j d : ℕ) (hi0 : 0 < i) (hj0 : 0 < j) (hd0 : 0 < d)
    (hi : D.p < i)
    (hj : j < D.q)
    (hib : i < D.B) (hjb : j < D.C)
    (hd : d < D.u)
    (he : (i : ℤ)*D.b+j*D.c =
      n+d*D.a) :
    rbAxisA D i j d ∈ returnIdeal (H) n ∧
    rbAxisB D i j d ∈ returnIdeal (H) n := by
  have hr := relations_int D
  have hs := D.coefficient_sums
  have hdC : d ≤ D.A := by omega
  have hAeq : rbAxisA D i j d =
      (i : ℤ)*D.b+(D.q : ℤ)*D.c-d*D.a := by
    unfold rbAxisA
    nlinarith only [hr.1]
  have hBeq : rbAxisB D i j d =
      (D.B : ℤ)*D.b+(j : ℤ)*D.c-d*D.a := by
    unfold rbAxisB
    nlinarith only [hr.2.1]
  constructor
  · rw [hAeq]
    apply boundary_mem D n i j d i (D.q) le_rfl (by omega) he
    rw [← hAeq]
    unfold rbAxisA
    apply combination_int D <;> omega
  · rw [hBeq]
    apply boundary_mem D n i j d (D.B) j (by omega) le_rfl he
    rw [← hBeq]
    unfold rbAxisB
    apply combination_int D <;> omega

theorem rb_return_three_generators (D : Positive H)
    (n i j d : ℕ) (hi0 : 0 < i) (hj0 : 0 < j) (hd0 : 0 < d)
    (hi : D.p < i)
    (hj : j < D.q)
    (hib : i < D.B) (hjb : j < D.C)
    (hd : d < D.u)
    (he : (i : ℤ)*D.b+j*D.c =
      n+d*D.a) (x : ℤ) :
    x ∈ returnIdeal (H) n ↔
    x-((i : ℤ)*D.b+j*D.c) ∈ (H).asRelativeIdeal ∨
    x-rbAxisA D i j d ∈ (H).asRelativeIdeal ∨
    x-rbAxisB D i j d ∈ (H).asRelativeIdeal := by
  have hr := relations_int D
  have hs := D.coefficient_sums
  have ha := rb_axes_mem D n i j d hi0 hj0 hd0 hi hj hib hjb hd he
  have hAeq : rbAxisA D i j d =
      (i : ℤ)*D.b+(D.q : ℤ)*D.c-d*D.a := by
    unfold rbAxisA
    nlinarith only [hr.1]
  have hBeq : rbAxisB D i j d =
      (D.B : ℤ)*D.b+(j : ℤ)*D.c-d*D.a := by
    unfold rbAxisB
    nlinarith only [hr.2.1]
  rw [hAeq, hBeq] at ha ⊢
  exact return_rectangle_cover D n i j d (D.B) (D.q) he
    (by intro u v hu hv; exact ⟨by omega, by omega, Or.inr hv⟩) ha.1 ha.2 x



end NS25Lean.GenericReturn
