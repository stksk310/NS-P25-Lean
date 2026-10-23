import NS25Lean.P3CanonicalReturnR59

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R61
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2B4AR1
open L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

theorem normalized_relations (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) :
    (criticalExponent M.base (e 0) : ℤ) * routingA M.base e =
      (P3R57.roleCoefficient M hp e 0 1 : ℤ) * routingB M.base e +
      (P3R57.roleCoefficient M hp e 0 2 : ℤ) * routingC M.base e ∧
    (criticalExponent M.base (e 1) : ℤ) * routingB M.base e =
      (P3R57.roleCoefficient M hp e 1 0 : ℤ) * routingA M.base e +
      (P3R57.roleCoefficient M hp e 1 2 : ℤ) * routingC M.base e ∧
    (criticalExponent M.base (e 2) : ℤ) * routingC M.base e =
      (P3R57.roleCoefficient M hp e 2 0 : ℤ) * routingA M.base e +
      (P3R57.roleCoefficient M hp e 2 1 : ℤ) * routingB M.base e := by
  have h := coherent_normalized_relations M.base e (P3R58.p3_coherentHerzogData M hp e)
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.1, by exact_mod_cast h.2.2⟩

theorem routing_combination_mem (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (k i j : ℤ) (hk : 0 ≤ k) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    k * routingA B e + i * routingB B e + j * routingC B e ∈
      (routingH B e).asRelativeIdeal := by
  refine ⟨k.toNat * routingA B e + i.toNat * routingB B e + j.toNat * routingC B e, ?_, ?_⟩
  · change _ ∈ generatedThree _ _ _
    exact (mem_generatedThree_iff _ _ _ _).2 ⟨_, _, _, rfl⟩
  · simp [Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hj]

theorem routing_factorization_int (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x : ℤ) (hx : x ∈ (routingH B e).asRelativeIdeal) :
    ∃ k i j : ℕ, x = (k : ℤ) * routingA B e + i * routingB B e + j * routingC B e := by
  obtain ⟨n, hn, he⟩ := hx
  obtain ⟨k, i, j, hf⟩ := routingH_factorization B e hn
  refine ⟨k, i, j, ?_⟩
  rw [he, hf]
  push_cast
  rfl

theorem ideal_add_int {H : NumericalSemigroup} (I : RelativeIdeal H)
    {x y : ℤ} (hx : x ∈ I) (hy : y ∈ H.asRelativeIdeal) : x+y ∈ I := by
  obtain ⟨n, hn, he⟩ := hy
  rw [he]
  exact I.add_mem hx hn

theorem canonical_not_positive_a (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (i j : ℕ) (hi : i < criticalExponent M.base (e 1))
    (hj : j < criticalExponent M.base (e 2))
    (hc : i < P3R57.roleCoefficient M hp e 0 1 ∨ j < P3R57.roleCoefficient M hp e 0 2)
    (k : ℤ) (hk : 0 < k) (y : ℤ) (hy : y ∈ (routingH M.base e).asRelativeIdeal) :
    (i : ℤ) * routingB M.base e + j * routingC M.base e ≠ k * routingA M.base e + y := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  intro he
  have hcan := P3R58.p3_lshape_canonical M hp e i j hi hj hc
  have hcan' : (i : ℤ) * routingB M.base e + j * routingC M.base e =
      (routingH M.base e).asRelativeIdeal.aperyRepresentative (routingA M.base e)
        (gridResidue M.base e i j) := by
    simpa [IsCanonicalTailGridPoint, normalizedGrid, physicalAlpha] using hcan
  have hm := ideal_add_int (routingH M.base e).asRelativeIdeal hy
    (routing_combination_mem M.base e (k-1) 0 0 (by omega) le_rfl le_rfl)
  have hprev := (routingH M.base e).asRelativeIdeal.aperyRepresentative_sub_modulus_not_mem
    (routingA M.base e) (gridResidue M.base e i j)
  apply hprev
  convert hm using 1
  rw [← hcan', he]
  ring



/-- Rectangle crossing supplies the exact two boundary common multiples. -/
theorem return_rectangle_cover (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n i j d ib jb : ℕ)
    (he : (i : ℤ) * routingB M.base e + j * routingC M.base e =
      (n * M.base.q.val : ℕ) + d * routingA M.base e)
    (hrect : ∀ u v : ℕ, u < ib → v < jb →
      u < criticalExponent M.base (e 1) ∧ v < criticalExponent M.base (e 2) ∧
      (u < P3R57.roleCoefficient M hp e 0 1 ∨ v < P3R57.roleCoefficient M hp e 0 2))
    (hA : (i : ℤ) * routingB M.base e + jb * routingC M.base e - d * routingA M.base e ∈
      returnIdeal (routingH M.base e) (n * M.base.q.val))
    (hB : (ib : ℤ) * routingB M.base e + j * routingC M.base e - d * routingA M.base e ∈
      returnIdeal (routingH M.base e) (n * M.base.q.val))
    (x : ℤ) :
    x ∈ returnIdeal (routingH M.base e) (n * M.base.q.val) ↔
    x - ((i : ℤ) * routingB M.base e + j * routingC M.base e) ∈ (routingH M.base e).asRelativeIdeal ∨
    x - ((i : ℤ) * routingB M.base e + jb * routingC M.base e - d * routingA M.base e) ∈ (routingH M.base e).asRelativeIdeal ∨
    x - ((ib : ℤ) * routingB M.base e + j * routingC M.base e - d * routingA M.base e) ∈ (routingH M.base e).asRelativeIdeal := by
  have hbeta : (i : ℤ) * routingB M.base e + j * routingC M.base e ∈
      returnIdeal (routingH M.base e) (n * M.base.q.val) := by
    rw [mem_returnIdeal_iff]
    refine ⟨?_, ?_⟩
    · simpa using routing_combination_mem M.base e 0 i j le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [he]
      convert routing_combination_mem M.base e d 0 0 (Nat.cast_nonneg _) le_rfl le_rfl using 1 <;> ring
  constructor
  · intro hx
    obtain ⟨A, B, C, hf⟩ := routing_factorization_int M.base e _ hx.2
    have heq : x + (d : ℤ) * routingA M.base e =
        (i : ℤ) * routingB M.base e + j * routingC M.base e +
        (A : ℤ) * routingA M.base e + B * routingB M.base e + C * routingC M.base e := by
      simp only [Nat.cast_mul] at hf he
      linarith
    by_cases hAd : d ≤ A
    · left
      convert routing_combination_mem M.base e ((A : ℤ)-d) B C (by omega) (Nat.cast_nonneg _) (Nat.cast_nonneg _) using 1 <;> nlinarith only [heq]
    · by_cases hbi : i + B < ib
      · by_cases hcj : j + C < jb
        · obtain ⟨hi, hj, hc⟩ := hrect _ _ hbi hcj
          exfalso
          apply canonical_not_positive_a M hp e (i+B) (j+C) hi hj hc ((d : ℤ)-A) (by omega) x hx.1
          simp only [Nat.cast_add]
          nlinarith only [heq]
        · right; left
          convert routing_combination_mem M.base e A B ((j : ℤ)+C-jb) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by omega) using 1 <;> nlinarith only [heq]
      · right; right
        convert routing_combination_mem M.base e A ((i : ℤ)+B-ib) C (Nat.cast_nonneg _) (by omega) (Nat.cast_nonneg _) using 1 <;> nlinarith only [heq]
  · intro hx
    rcases hx with hx | hx | hx
    · have hm := ideal_add_int (returnIdeal (routingH M.base e) (n*M.base.q.val)) hbeta hx
      convert hm using 1 <;> ring
    · have hm := ideal_add_int (returnIdeal (routingH M.base e) (n*M.base.q.val)) hA hx
      convert hm using 1 <;> ring
    · have hm := ideal_add_int (returnIdeal (routingH M.base e) (n*M.base.q.val)) hB hx
      convert hm using 1 <;> ring


theorem boundary_mem (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (n i j d ib jb : ℕ) (hij : i ≤ ib) (hjj : j ≤ jb)
    (he : (i : ℤ)*routingB B e+j*routingC B e = (n*B.q.val : ℕ)+d*routingA B e)
    (hmem : (ib : ℤ)*routingB B e+jb*routingC B e-d*routingA B e ∈ (routingH B e).asRelativeIdeal) :
    (ib : ℤ)*routingB B e+jb*routingC B e-d*routingA B e ∈ returnIdeal (routingH B e) (n*B.q.val) := by
  refine ⟨hmem, ?_⟩
  change (ib : ℤ)*routingB B e+jb*routingC B e-d*routingA B e-(n*B.q.val : ℕ) ∈ (routingH B e).asRelativeIdeal
  convert routing_combination_mem B e 0 ((ib : ℤ)-i) ((jb : ℤ)-j)
    le_rfl (by omega) (by omega) using 1 <;> nlinarith only [he]

def ltAxisA (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (i j d : ℕ) : ℤ :=
  ((P3R57.roleCoefficient M hp e 2 0 : ℤ)-d)*routingA M.base e + ((i : ℤ)+P3R57.roleCoefficient M hp e 2 1)*routingB M.base e + (0)*routingC M.base e

def ltAxisB (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (i j d : ℕ) : ℤ :=
  ((criticalExponent M.base (e 0) : ℤ)-d)*routingA M.base e + (0)*routingB M.base e + ((j : ℤ)-P3R57.roleCoefficient M hp e 0 2)*routingC M.base e

theorem lt_axes_mem (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n i j d : ℕ) (hi0 : 0 < i) (hj0 : 0 < j) (hd0 : 0 < d)
    (hi : i < P3R57.roleCoefficient M hp e 0 1)
    (hj : P3R57.roleCoefficient M hp e 0 2 < j)
    (hib : i < criticalExponent M.base (e 1)) (hjb : j < criticalExponent M.base (e 2))
    (hd : d < P3R57.roleCoefficient M hp e 2 0)
    (he : (i : ℤ)*routingB M.base e+j*routingC M.base e =
      (n*M.base.q.val : ℕ)+d*routingA M.base e) :
    ltAxisA M hp e i j d ∈ returnIdeal (routingH M.base e) (n*M.base.q.val) ∧
    ltAxisB M hp e i j d ∈ returnIdeal (routingH M.base e) (n*M.base.q.val) := by
  have hr := normalized_relations M hp e
  have hs := P3R58.p3_coefficient_sums M hp e
  have hdC : d ≤ criticalExponent M.base (e 0) := by omega
  have hAeq : ltAxisA M hp e i j d =
      (i : ℤ)*routingB M.base e+(criticalExponent M.base (e 2) : ℤ)*routingC M.base e-d*routingA M.base e := by
    unfold ltAxisA
    nlinarith only [hr.2.2]
  have hBeq : ltAxisB M hp e i j d =
      (P3R57.roleCoefficient M hp e 0 1 : ℤ)*routingB M.base e+(j : ℤ)*routingC M.base e-d*routingA M.base e := by
    unfold ltAxisB
    nlinarith only [hr.1]
  constructor
  · rw [hAeq]
    apply boundary_mem M.base e n i j d i (criticalExponent M.base (e 2)) le_rfl (by omega) he
    rw [← hAeq]
    unfold ltAxisA
    apply routing_combination_mem <;> omega
  · rw [hBeq]
    apply boundary_mem M.base e n i j d (P3R57.roleCoefficient M hp e 0 1) j (by omega) le_rfl he
    rw [← hBeq]
    unfold ltAxisB
    apply routing_combination_mem <;> omega

theorem lt_return_three_generators (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n i j d : ℕ) (hi0 : 0 < i) (hj0 : 0 < j) (hd0 : 0 < d)
    (hi : i < P3R57.roleCoefficient M hp e 0 1)
    (hj : P3R57.roleCoefficient M hp e 0 2 < j)
    (hib : i < criticalExponent M.base (e 1)) (hjb : j < criticalExponent M.base (e 2))
    (hd : d < P3R57.roleCoefficient M hp e 2 0)
    (he : (i : ℤ)*routingB M.base e+j*routingC M.base e =
      (n*M.base.q.val : ℕ)+d*routingA M.base e) (x : ℤ) :
    x ∈ returnIdeal (routingH M.base e) (n*M.base.q.val) ↔
    x-((i : ℤ)*routingB M.base e+j*routingC M.base e) ∈ (routingH M.base e).asRelativeIdeal ∨
    x-ltAxisA M hp e i j d ∈ (routingH M.base e).asRelativeIdeal ∨
    x-ltAxisB M hp e i j d ∈ (routingH M.base e).asRelativeIdeal := by
  have hr := normalized_relations M hp e
  have hs := P3R58.p3_coefficient_sums M hp e
  have ha := lt_axes_mem M hp e n i j d hi0 hj0 hd0 hi hj hib hjb hd he
  have hAeq : ltAxisA M hp e i j d =
      (i : ℤ)*routingB M.base e+(criticalExponent M.base (e 2) : ℤ)*routingC M.base e-d*routingA M.base e := by
    unfold ltAxisA
    nlinarith only [hr.2.2]
  have hBeq : ltAxisB M hp e i j d =
      (P3R57.roleCoefficient M hp e 0 1 : ℤ)*routingB M.base e+(j : ℤ)*routingC M.base e-d*routingA M.base e := by
    unfold ltAxisB
    nlinarith only [hr.1]
  rw [hAeq, hBeq] at ha ⊢
  exact return_rectangle_cover M hp e n i j d (P3R57.roleCoefficient M hp e 0 1) (criticalExponent M.base (e 2)) he
    (by intro u v hu hv; exact ⟨by omega, by omega, Or.inl hu⟩) ha.1 ha.2 x

def rbAxisA (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (i j d : ℕ) : ℤ :=
  ((criticalExponent M.base (e 0) : ℤ)-d)*routingA M.base e + ((i : ℤ)-P3R57.roleCoefficient M hp e 0 1)*routingB M.base e + (0)*routingC M.base e

def rbAxisB (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (i j d : ℕ) : ℤ :=
  ((P3R57.roleCoefficient M hp e 1 0 : ℤ)-d)*routingA M.base e + (0)*routingB M.base e + ((j : ℤ)+P3R57.roleCoefficient M hp e 1 2)*routingC M.base e

theorem rb_axes_mem (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n i j d : ℕ) (hi0 : 0 < i) (hj0 : 0 < j) (hd0 : 0 < d)
    (hi : P3R57.roleCoefficient M hp e 0 1 < i)
    (hj : j < P3R57.roleCoefficient M hp e 0 2)
    (hib : i < criticalExponent M.base (e 1)) (hjb : j < criticalExponent M.base (e 2))
    (hd : d < P3R57.roleCoefficient M hp e 1 0)
    (he : (i : ℤ)*routingB M.base e+j*routingC M.base e =
      (n*M.base.q.val : ℕ)+d*routingA M.base e) :
    rbAxisA M hp e i j d ∈ returnIdeal (routingH M.base e) (n*M.base.q.val) ∧
    rbAxisB M hp e i j d ∈ returnIdeal (routingH M.base e) (n*M.base.q.val) := by
  have hr := normalized_relations M hp e
  have hs := P3R58.p3_coefficient_sums M hp e
  have hdC : d ≤ criticalExponent M.base (e 0) := by omega
  have hAeq : rbAxisA M hp e i j d =
      (i : ℤ)*routingB M.base e+(P3R57.roleCoefficient M hp e 0 2 : ℤ)*routingC M.base e-d*routingA M.base e := by
    unfold rbAxisA
    nlinarith only [hr.1]
  have hBeq : rbAxisB M hp e i j d =
      (criticalExponent M.base (e 1) : ℤ)*routingB M.base e+(j : ℤ)*routingC M.base e-d*routingA M.base e := by
    unfold rbAxisB
    nlinarith only [hr.2.1]
  constructor
  · rw [hAeq]
    apply boundary_mem M.base e n i j d i (P3R57.roleCoefficient M hp e 0 2) le_rfl (by omega) he
    rw [← hAeq]
    unfold rbAxisA
    apply routing_combination_mem <;> omega
  · rw [hBeq]
    apply boundary_mem M.base e n i j d (criticalExponent M.base (e 1)) j (by omega) le_rfl he
    rw [← hBeq]
    unfold rbAxisB
    apply routing_combination_mem <;> omega

theorem rb_return_three_generators (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n i j d : ℕ) (hi0 : 0 < i) (hj0 : 0 < j) (hd0 : 0 < d)
    (hi : P3R57.roleCoefficient M hp e 0 1 < i)
    (hj : j < P3R57.roleCoefficient M hp e 0 2)
    (hib : i < criticalExponent M.base (e 1)) (hjb : j < criticalExponent M.base (e 2))
    (hd : d < P3R57.roleCoefficient M hp e 1 0)
    (he : (i : ℤ)*routingB M.base e+j*routingC M.base e =
      (n*M.base.q.val : ℕ)+d*routingA M.base e) (x : ℤ) :
    x ∈ returnIdeal (routingH M.base e) (n*M.base.q.val) ↔
    x-((i : ℤ)*routingB M.base e+j*routingC M.base e) ∈ (routingH M.base e).asRelativeIdeal ∨
    x-rbAxisA M hp e i j d ∈ (routingH M.base e).asRelativeIdeal ∨
    x-rbAxisB M hp e i j d ∈ (routingH M.base e).asRelativeIdeal := by
  have hr := normalized_relations M hp e
  have hs := P3R58.p3_coefficient_sums M hp e
  have ha := rb_axes_mem M hp e n i j d hi0 hj0 hd0 hi hj hib hjb hd he
  have hAeq : rbAxisA M hp e i j d =
      (i : ℤ)*routingB M.base e+(P3R57.roleCoefficient M hp e 0 2 : ℤ)*routingC M.base e-d*routingA M.base e := by
    unfold rbAxisA
    nlinarith only [hr.1]
  have hBeq : rbAxisB M hp e i j d =
      (criticalExponent M.base (e 1) : ℤ)*routingB M.base e+(j : ℤ)*routingC M.base e-d*routingA M.base e := by
    unfold rbAxisB
    nlinarith only [hr.2.1]
  rw [hAeq, hBeq] at ha ⊢
  exact return_rectangle_cover M hp e n i j d (criticalExponent M.base (e 1)) (P3R57.roleCoefficient M hp e 0 2) he
    (by intro u v hu hv; exact ⟨by omega, by omega, Or.inr hv⟩) ha.1 ha.2 x


end NS25Lean.P3R61
