import NS25Lean.P3CommonArmR59

set_option linter.style.header false
set_option autoImplicit false

namespace NS25Lean.P3R60

/-- The initial gate height followed by the actual defects at levels `1,...,n`. -/
def runningMinimum (C : ℕ) (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => C
  | n + 1 => min (runningMinimum C d n) (d (n + 1))

theorem le_runningMinimum_iff (C : ℕ) (d : ℕ → ℕ) (n k : ℕ) :
    k ≤ runningMinimum C d n ↔
      k ≤ C ∧ ∀ r : ℕ, 0 < r → r ≤ n → k ≤ d r := by
  induction n with
  | zero =>
    change k ≤ C ↔ k ≤ C ∧ ∀ r : ℕ, 0 < r → r ≤ 0 → k ≤ d r
    constructor
    · intro h
      refine ⟨h, ?_⟩
      intro r hr hrn
      omega
    · intro h
      exact h.1
  | succ n ih =>
    rw [runningMinimum, le_min_iff, ih]
    constructor
    · rintro ⟨⟨hC, hprev⟩, hlast⟩
      refine ⟨hC, ?_⟩
      intro r hr hrn
      by_cases hle : r ≤ n
      · exact hprev r hr hle
      · have he : r = n + 1 := by omega
        simpa [he] using hlast
    · rintro ⟨hC, hall⟩
      exact ⟨⟨hC, fun r hr hrn => hall r hr (by omega)⟩,
        hall (n + 1) (by omega) (by omega)⟩

theorem runningMinimum_le_iff (C : ℕ) (d : ℕ → ℕ) (n k : ℕ) :
    runningMinimum C d n ≤ k ↔
      C ≤ k ∨ ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ d r ≤ k := by
  induction n with
  | zero => simp [runningMinimum]
  | succ n ih =>
    rw [runningMinimum, min_le_iff, ih]
    constructor
    · rintro ((hC | ⟨r, hr, hrn, hd⟩) | hlast)
      · exact Or.inl hC
      · exact Or.inr ⟨r, hr, by omega, hd⟩
      · exact Or.inr ⟨n + 1, by omega, by omega, hlast⟩
    · rintro (hC | ⟨r, hr, hrn, hd⟩)
      · exact Or.inl (Or.inl hC)
      · by_cases hle : r ≤ n
        · exact Or.inl (Or.inr ⟨r, hr, hle, hd⟩)
        · have he : r = n + 1 := by omega
          exact Or.inr (by simpa [he] using hd)

/-- Positive birth height is exactly the strict running-minimum criterion. -/
theorem record_height_pos_iff (C : ℕ) (d : ℕ → ℕ) (q : ℕ) (hq : 0 < q) :
    0 < runningMinimum C d (q - 1) - d q ↔
      d q < C ∧ ∀ r : ℕ, 0 < r → r < q → d q < d r := by
  constructor
  · intro hpos
    have hle : d q + 1 ≤ runningMinimum C d (q - 1) := by omega
    obtain ⟨hC, hall⟩ := (le_runningMinimum_iff C d (q - 1) (d q + 1)).mp hle
    refine ⟨by omega, ?_⟩
    intro r hr hrq
    have hd := hall r hr (by omega)
    omega
  · rintro ⟨hC, hall⟩
    have hle : d q + 1 ≤ runningMinimum C d (q - 1) := by
      apply (le_runningMinimum_iff C d (q - 1) (d q + 1)).mpr
      refine ⟨by omega, ?_⟩
      intro r hr hrq
      have hd := hall r hr (by omega)
      omega
    omega

end NS25Lean.P3R60

