import NS25Lean.P2SectorCCriticalComponent

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4C

open FourGeneratedBridge L2B L5A1 L5A2C3G L5A2C4A L5A2C4B ChosenBase

variable {Gamma : NumericalSemigroup}

/-- The actual degree represented by paper coordinates `(n,i,j)` after the
frozen `a,b,c` reindexing. -/
def gridDegree (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (n i j : ℕ) : ℕ :=
  n * weights B (e 0) + i * weights B (e 1) + j * weights B (e 2)

private theorem gridDegree_mem_H (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (n i j : ℕ) : gridDegree B e n i j ∈ B.H := by
  have hn := B.H.nsmul_mem (B.tailDegrees (e 0)).property n
  have hi := B.H.nsmul_mem (B.tailDegrees (e 1)).property i
  have hj := B.H.nsmul_mem (B.tailDegrees (e 2)).property j
  simpa [gridDegree, weights, nsmul_eq_mul, Nat.add_assoc] using
    B.H.add_mem (B.H.add_mem hn hi) hj

/-- Every reindexed `(b,c)` column eventually enters the actual Apéry tail
when moved in the positive `a` direction. -/
theorem exists_gridDegree_mem_K (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j : ℕ) : ∃ n : ℕ, gridDegree B e n i j ∈ B.K := by
  obtain ⟨conductor, hconductor⟩ := Gamma.exists_conductor
  refine ⟨conductor + B.q.val, ?_⟩
  have ha := weights_positive B (e 0)
  have hq : B.q.val ≤ gridDegree B e (conductor + B.q.val) i j := by
    unfold gridDegree
    nlinarith
  have hlarge : conductor + B.q.val ≤
      gridDegree B e (conductor + B.q.val) i j := by
    unfold gridDegree
    nlinarith
  have hc : conductor ≤ gridDegree B e (conductor + B.q.val) i j - B.q.val := by
    omega
  exact ⟨gridDegree_mem_H B e _ _ _, hq, hconductor _ hc⟩

/-- Historical `eta_{i,j}`: the least actual `a`-exponent whose reindexed
degree belongs to the chosen-base Apéry tail `K`. -/
def eta (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_gridDegree_mem_K B e i j)

theorem eta_mem_K (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    gridDegree B e (eta B e i j) i j ∈ B.K := by
  classical
  exact Nat.find_spec (exists_gridDegree_mem_K B e i j)

theorem eta_le_of_mem (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j n : ℕ)
    (h : gridDegree B e n i j ∈ B.K) : eta B e i j ≤ n := by
  classical
  exact Nat.find_min' (exists_gridDegree_mem_K B e i j) h

/-- Exact threshold characterization of the actual `eta` value.  This is the
kernel bridge from the least-number definition back to membership in `K`; no
threshold property is stored as input data. -/
theorem gridDegree_mem_K_iff_eta_le (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j n : ℕ) : gridDegree B e n i j ∈ B.K ↔ eta B e i j ≤ n := by
  constructor
  · exact eta_le_of_mem B e i j n
  · intro heta
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le heta
    have hadd := aperyTail_add_mem B.H_le (eta_mem_K B e i j)
      (B.H.nsmul_mem (B.tailDegrees (e 0)).property d)
    change gridDegree B e (eta B e i j) i j +
        d * weights B (e 0) ∈ B.K at hadd
    have heq : gridDegree B e (eta B e i j + d) i j =
        gridDegree B e (eta B e i j) i j + d * weights B (e 0) := by
      simp [gridDegree, Nat.add_mul]
      omega
    rwa [heq]

/-- In particular, height zero is equivalent to membership of the actual
bottom point of the reindexed column. -/
theorem eta_eq_zero_iff (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    eta B e i j = 0 ↔ gridDegree B e 0 i j ∈ B.K := by
  rw [gridDegree_mem_K_iff_eta_le]
  omega

/-- Adding `b`-weight can only lower the least required `a`-height. -/
theorem eta_antitone_left (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j di : ℕ) : eta B e (i + di) j ≤ eta B e i j := by
  apply eta_le_of_mem
  have hadd := aperyTail_add_mem B.H_le (eta_mem_K B e i j)
    (B.H.nsmul_mem (B.tailDegrees (e 1)).property di)
  change gridDegree B e (eta B e i j) i j +
      di * weights B (e 1) ∈ B.K at hadd
  have heq : gridDegree B e (eta B e i j) (i + di) j =
      gridDegree B e (eta B e i j) i j + di * weights B (e 1) := by
    simp [gridDegree, Nat.add_mul]
    omega
  rw [heq]
  exact hadd

/-- Adding `c`-weight can only lower the least required `a`-height. -/
theorem eta_antitone_right (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j dj : ℕ) : eta B e i (j + dj) ≤ eta B e i j := by
  apply eta_le_of_mem
  have hadd := aperyTail_add_mem B.H_le (eta_mem_K B e i j)
    (B.H.nsmul_mem (B.tailDegrees (e 2)).property dj)
  change gridDegree B e (eta B e i j) i j +
      dj * weights B (e 2) ∈ B.K at hadd
  have heq : gridDegree B e (eta B e i j) i (j + dj) =
      gridDegree B e (eta B e i j) i j + dj * weights B (e 2) := by
    simp [gridDegree, Nat.add_mul]
    omega
  rw [heq]
  exact hadd

abbrev H0 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := eta B e 0 0
abbrev P1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  eta B e (r12 B e - 1) (r13 B e)
abbrev Q1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  eta B e (r12 B e) (r13 B e - 1)
abbrev Y3 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  eta B e 0 (c3 B e - 1)
abbrev Z3 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  eta B e (r32 B e) 0
abbrev Z3minus (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  eta B e (r32 B e - 1) 0

/-- The repaired paper coordinate of the first direct-PF corner. -/
def kappa1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) : ℕ × ℕ :=
  (c2 B e - 1, r13 B e - 1)

end NS25Lean.L5A2C4C
