import NS25Lean.FourGeneratedBridge
import Mathlib.NumberTheory.FrobeniusNumber

set_option linter.style.header false

namespace NS25Lean.FourGeneratedBridge

/-- A minimal four-generator presentation. No ordering of the tail is needed.
The result therefore also applies when `m` is the multiplicity. -/
structure IsMinimallyGeneratedByFour (Gamma : NumericalSemigroup)
    (m n₁ n₂ n₃ : ℕ) : Prop where
  generated : Gamma.toAddSubmonoid = generatedFour m n₁ n₂ n₃
  m_pos : 0 < m
  n₁_pos : 0 < n₁
  n₂_pos : 0 < n₂
  n₃_pos : 0 < n₃
  m_minimal : m ∉ generatedThree n₁ n₂ n₃
  n₁_minimal : n₁ ∉ generatedThree m n₂ n₃
  n₂_minimal : n₂ ∉ generatedThree m n₁ n₃
  n₃_minimal : n₃ ∉ generatedThree m n₁ n₂

def tailGcd (n₁ n₂ n₃ : ℕ) : ℕ := Nat.gcd n₁ (Nat.gcd n₂ n₃)

theorem tailGcd_pos {n₁ n₂ n₃ : ℕ} (h : 0 < n₁) : 0 < tailGcd n₁ n₂ n₃ :=
  Nat.gcd_pos_of_pos_left _ h

theorem tailGcd_dvd (n₁ n₂ n₃ : ℕ) :
    tailGcd n₁ n₂ n₃ ∣ n₁ ∧ tailGcd n₁ n₂ n₃ ∣ n₂ ∧
      tailGcd n₁ n₂ n₃ ∣ n₃ :=
  ⟨Nat.gcd_dvd_left _ _, dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _),
    dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)⟩

theorem normalized_gcd_eq_one {n₁ n₂ n₃ : ℕ} (h : 0 < n₁) :
    Nat.gcd (n₁ / tailGcd n₁ n₂ n₃)
      (Nat.gcd (n₂ / tailGcd n₁ n₂ n₃) (n₃ / tailGcd n₁ n₂ n₃)) = 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := tailGcd_dvd n₁ n₂ n₃
  rw [Nat.gcd_div h₂ h₃, Nat.gcd_div h₁ (Nat.dvd_gcd h₂ h₃)]
  exact Nat.div_self (tailGcd_pos h)

theorem quotient_pos_of_dvd {d n : ℕ} (hn : 0 < n) (h : d ∣ n) : 0 < n / d := by
  have heq := Nat.mul_div_cancel' h
  by_contra hnot
  have hz : n / d = 0 := Nat.eq_zero_of_not_pos hnot
  rw [hz, Nat.mul_zero] at heq
  omega

theorem mem_generatedThree_iff (a b c x : ℕ) :
    x ∈ generatedThree a b c ↔ ∃ p q r : ℕ, x = p * a + q * b + r * c := by
  constructor
  · intro hx
    induction hx using AddSubmonoid.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨p, q, r, rfl⟩ := ihx
      obtain ⟨s, t, u, rfl⟩ := ihy
      exact ⟨p + s, q + t, r + u, by ring⟩
  · rintro ⟨p, q, r, rfl⟩
    exact AddSubmonoid.add_mem _ (AddSubmonoid.add_mem _
      (AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (by simp)) p)
      (AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (by simp)) q))
      (AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (by simp)) r)

theorem generatedThree_scale (d a b c x : ℕ) :
    x ∈ generatedThree (d * a) (d * b) (d * c) ↔
      ∃ y ∈ generatedThree a b c, x = d * y := by
  simp only [mem_generatedThree_iff]
  constructor
  · rintro ⟨p, q, r, rfl⟩
    exact ⟨p * a + q * b + r * c, ⟨p, q, r, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨p, q, r, rfl⟩, rfl⟩
    exact ⟨p, q, r, by ring⟩

theorem generatedThree_mul_mem_iff {d : ℕ} (hd : 0 < d) (a b c x : ℕ) :
    d * x ∈ generatedThree (d * a) (d * b) (d * c) ↔
      x ∈ generatedThree a b c := by
  rw [generatedThree_scale]
  constructor
  · rintro ⟨y, hy, heq⟩
    have : x = y := Nat.eq_of_mul_eq_mul_left hd heq
    simpa [this] using hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

theorem setGcd_three (a b c : ℕ) : Nat.setGcd {a, b, c} = Nat.gcd a (Nat.gcd b c) := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (Nat.setGcd_dvd_of_mem (by simp))
      (Nat.dvd_gcd (Nat.setGcd_dvd_of_mem (by simp))
        (Nat.setGcd_dvd_of_mem (by simp)))
  · apply Nat.dvd_setGcd_iff.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    obtain ⟨h₁, h₂, h₃⟩ := tailGcd_dvd a b c
    rcases hx with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃

theorem generatedThree_finite_compl {a b c : ℕ} (h : Nat.gcd a (Nat.gcd b c) = 1) :
    Set.Finite {x | x ∉ generatedThree a b c} := by
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge {a, b, c}
  apply (Set.finite_lt_nat N).subset
  intro x hx
  by_contra hn
  exact hx (hN x (by simpa using hn) (by simp [setGcd_three, h]))

/-- The actual gcd-normalized numerical semigroup. -/
def normalizedSemigroup (n₁ n₂ n₃ : ℕ) (h : 0 < n₁) : NumericalSemigroup where
  toAddSubmonoid := generatedThree (n₁ / tailGcd n₁ n₂ n₃)
    (n₂ / tailGcd n₁ n₂ n₃) (n₃ / tailGcd n₁ n₂ n₃)
  finite_compl := generatedThree_finite_compl (normalized_gcd_eq_one h)

theorem normalizedSemigroup_scale (n₁ n₂ n₃ : ℕ) (h : 0 < n₁) (x : ℕ) :
    x ∈ generatedThree n₁ n₂ n₃ ↔
      ∃ y ∈ normalizedSemigroup n₁ n₂ n₃ h, x = tailGcd n₁ n₂ n₃ * y := by
  obtain ⟨h₁, h₂, h₃⟩ := tailGcd_dvd n₁ n₂ n₃
  change x ∈ generatedThree n₁ n₂ n₃ ↔
    ∃ y ∈ generatedThree (n₁ / tailGcd n₁ n₂ n₃)
      (n₂ / tailGcd n₁ n₂ n₃) (n₃ / tailGcd n₁ n₂ n₃), x = tailGcd n₁ n₂ n₃ * y
  have hs := generatedThree_scale (tailGcd n₁ n₂ n₃)
    (n₁ / tailGcd n₁ n₂ n₃) (n₂ / tailGcd n₁ n₂ n₃)
    (n₃ / tailGcd n₁ n₂ n₃) x
  simpa only [Nat.mul_div_cancel' h₁, Nat.mul_div_cancel' h₂,
    Nat.mul_div_cancel' h₃] using hs

theorem mul_mem_closure_pair {a b x : ℕ} (hx : x ∈ AddSubmonoid.closure ({a, b} : Set ℕ))
    (d : ℕ) : d * x ∈ AddSubmonoid.closure ({d * a, d * b} : Set ℕ) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
    apply AddSubmonoid.subset_closure
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rcases hy with rfl | rfl <;> simp
  | zero => simpa using (AddSubmonoid.zero_mem (AddSubmonoid.closure ({d*a,d*b} : Set ℕ)))
  | add x y hx hy ihx ihy => simpa [Nat.mul_add] using AddSubmonoid.add_mem _ ihx ihy

theorem normalizedSemigroup_minimal {Gamma : NumericalSemigroup} {m n₁ n₂ n₃ : ℕ}
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    (normalizedSemigroup n₁ n₂ n₃ h.n₁_pos).IsMinimallyGeneratedByThree
      (n₁ / tailGcd n₁ n₂ n₃) (n₂ / tailGcd n₁ n₂ n₃) (n₃ / tailGcd n₁ n₂ n₃) := by
  obtain ⟨h₁, h₂, h₃⟩ := tailGcd_dvd n₁ n₂ n₃
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro hx
    have hs := mul_mem_closure_pair hx (tailGcd n₁ n₂ n₃)
    simp only [Nat.mul_div_cancel' h₁, Nat.mul_div_cancel' h₂, Nat.mul_div_cancel' h₃] at hs
    exact h.n₁_minimal (AddSubmonoid.closure_mono (by simp) hs)
  · intro hx
    have hs := mul_mem_closure_pair hx (tailGcd n₁ n₂ n₃)
    simp only [Nat.mul_div_cancel' h₁, Nat.mul_div_cancel' h₂, Nat.mul_div_cancel' h₃] at hs
    exact h.n₂_minimal (AddSubmonoid.closure_mono (by simp) hs)
  · intro hx
    have hs := mul_mem_closure_pair hx (tailGcd n₁ n₂ n₃)
    simp only [Nat.mul_div_cancel' h₁, Nat.mul_div_cancel' h₂, Nat.mul_div_cancel' h₃] at hs
    exact h.n₃_minimal (AddSubmonoid.closure_mono (by simp) hs)

end NS25Lean.FourGeneratedBridge
