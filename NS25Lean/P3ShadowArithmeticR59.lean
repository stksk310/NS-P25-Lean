import NS25Lean.P3StrictReturnFormsR58

set_option linter.style.header false
namespace NS25Lean.P3R59

/-- The two positive head coordinates force a positive first lattice parameter. -/
theorem lattice_head_lambda_pos (P Q V Z B B' C' l k : ℤ)
    (hP : 0 < P) (hQ : 0 < Q) (hV : 0 < V) (hZ : 0 < Z)
    (hB : B ≤ Z) (hB' : 0 < B') (hC' : 0 < C')
    (heB : B' = B + P*l - Z*k) (heC : C' = Q*l + (Q+V)*k) : 0 < l := by
  by_contra hn
  have hl : l ≤ 0 := by omega
  by_cases hk : k ≤ 0
  · have hQl := mul_nonpos_of_nonneg_of_nonpos hQ.le hl
    have hQVk := mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ Q+V) hk
    linarith
  · have hk1 : 1 ≤ k := by omega
    have hPl := mul_nonpos_of_nonneg_of_nonpos hP.le hl
    have hZk : Z ≤ Z*k := by nlinarith
    linarith

/-- The c-head gives a lower bound for the sum of the integral lattice parameters. -/
theorem lattice_head_sum_pos (Q V C' l k : ℤ) (hQ : 0 < Q) (hV : 0 < V)
    (hl : 0 < l) (hC : 0 < C') (heC : C' = Q*l + (Q+V)*k) : 0 < l+k := by
  by_cases hk : 0 < k
  · omega
  · have hk0 : k ≤ 0 := by omega
    by_contra hn
    have hsum : l+k ≤ 0 := by omega
    have hQsum := mul_nonpos_of_nonneg_of_nonpos hQ.le hsum
    have hVk := mul_nonpos_of_nonneg_of_nonpos hV.le hk0
    nlinarith only [heC, hC, hQsum, hVk]

/-- The LT head is strictly beyond Q, giving the extra integral step lambda+kappa>=2. -/
theorem lattice_lt_head_sum (Q V C' l k : ℤ) (hQ : 0 < Q) (hV : 0 < V)
    (hl : 0 < l) (hC : Q < C') (heC : C' = Q*l + (Q+V)*k) : 2 ≤ l+k := by
  by_cases hk : 0 < k
  · omega
  · have hk0 : k ≤ 0 := by omega
    by_contra hn
    have hsum : l+k-1 ≤ 0 := by omega
    have hQsum := mul_nonpos_of_nonneg_of_nonpos hQ.le hsum
    have hVk := mul_nonpos_of_nonneg_of_nonpos hV.le hk0
    nlinarith only [heC, hC, hQsum, hVk]

/-- RB mixed-predecessor shadow barrier, with the exact strict A<C1 bound. -/
theorem rb_shadow_arithmetic (P Q U V W Z A B A' B' C' l k : ℤ)
    (hP : 0 < P) (hQ : 0 < Q) (hU : 0 < U) (hV : 0 < V)
    (hW : 0 < W) (hZ : 0 < Z) (hA : A < U+W) (hB : B ≤ Z)
    (hA' : 0 ≤ A') (hB' : 0 < B') (hC' : 0 < C')
    (heA : A' = A-(U+W)*l-W*k)
    (heB : B' = B+P*l-Z*k) (heC : C' = Q*l+(Q+V)*k) : False := by
  have hl := lattice_head_lambda_pos P Q V Z B B' C' l k hP hQ hV hZ hB hB' hC' heB heC
  have hsum := lattice_head_sum_pos Q V C' l k hQ hV hl hC' heC
  have hUl : U ≤ U*l := by nlinarith
  have hWsum : W ≤ W*(l+k) := by nlinarith
  nlinarith only [heA, hA, hA', hUl, hWsum]

/-- LT mixed-predecessor shadow barrier; the strict A<2W bound includes d<W. -/
theorem lt_shadow_arithmetic (P Q U V W Z A B A' B' C' l k : ℤ)
    (hP : 0 < P) (hQ : 0 < Q) (hU : 0 < U) (hV : 0 < V)
    (hW : 0 < W) (hZ : 0 < Z) (hA : A < 2*W) (hB : B ≤ Z)
    (hA' : 0 ≤ A') (hB' : 0 < B') (hC' : Q < C')
    (heA : A' = A-(U+W)*l-W*k)
    (heB : B' = B+P*l-Z*k) (heC : C' = Q*l+(Q+V)*k) : False := by
  have hl := lattice_head_lambda_pos P Q V Z B B' C' l k hP hQ hV hZ hB hB'
    (by omega) heB heC
  have hsum := lattice_lt_head_sum Q V C' l k hQ hV hl hC' heC
  have hUl : 0 ≤ U*l := by positivity
  have hWsum : 2*W ≤ W*(l+k) := by nlinarith
  nlinarith only [heA, hA, hA', hUl, hWsum]

/-- Exhaustive integral sign sectors for the third actual critical fiber. -/
theorem h3_fiber_arithmetic (P Q U V W Z A' B' C' l k : ℤ)
    (hP : 0 < P) (hQ : 0 < Q) (hU : 0 < U) (hV : 0 < V)
    (hW : 0 < W) (hZ : 0 < Z) (hA' : 0 ≤ A') (hB' : 0 ≤ B') (hC' : 0 ≤ C')
    (heA : A' = W-(U+W)*l-W*k)
    (heB : B' = Z+P*l-Z*k) (heC : C' = Q*l+(Q+V)*k) :
    (A'=W ∧ B'=Z ∧ C'=0) ∨ (A'=0 ∧ B'=0 ∧ C'=Q+V) := by
  by_cases hl : l ≤ 0
  · by_cases hk : k ≤ 0
    · have hQl := mul_nonpos_of_nonneg_of_nonpos hQ.le hl
      have hQVk := mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ Q+V) hk
      have hl0 : l=0 := by
        by_contra hn
        have hneg := mul_neg_of_pos_of_neg hQ (by omega : l<0)
        linarith
      have hk0 : k=0 := by
        by_contra hn
        have hneg := mul_neg_of_pos_of_neg (by omega : 0<Q+V) (by omega : k<0)
        linarith
      left
      simp only [hl0, hk0, mul_zero, sub_zero, add_zero] at heA heB heC
      exact ⟨heA,heB,heC⟩
    · have hk1 : 1 ≤ k := by omega
      have hPl := mul_nonpos_of_nonneg_of_nonpos hP.le hl
      have hZk : Z ≤ Z*k := by nlinarith
      have hl0 : l=0 := by
        by_contra hn
        have hneg := mul_neg_of_pos_of_neg hP (by omega : l<0)
        linarith
      have hkEq : k=1 := by
        by_contra hn
        have hk2 : 2 ≤ k := by omega
        have hZk2 : 2*Z ≤ Z*k := by nlinarith
        linarith
      right
      simp only [hl0, hkEq, mul_zero, mul_one, sub_zero, sub_self, add_zero, zero_add] at heA heB heC
      exact ⟨heA,heB,heC⟩
  · have hl1 : 1 ≤ l := by omega
    by_cases hk : 0 ≤ k
    · have hUl : U ≤ U*l := by nlinarith
      have hWl : W ≤ W*l := by nlinarith
      have hWk : 0 ≤ W*k := by positivity
      exfalso
      nlinarith only [heA, hA', hU, hUl, hWl, hWk]
    · have hkneg : k<0 := by omega
      have hsum : 1 ≤ l+k := by
        by_contra hn
        have hQsum := mul_nonpos_of_nonneg_of_nonpos hQ.le (by omega : l+k≤0)
        have hVk := mul_neg_of_pos_of_neg hV hkneg
        nlinarith only [heC, hC', hQsum, hVk]
      have hUl : U ≤ U*l := by nlinarith
      have hWsum : W ≤ W*(l+k) := by nlinarith
      exfalso
      nlinarith only [heA, hA', hU, hUl, hWsum]

end NS25Lean.P3R59
