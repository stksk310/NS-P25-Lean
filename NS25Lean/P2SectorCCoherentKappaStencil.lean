import NS25Lean.P2SectorCCoherentHerzog

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4E

open FourGeneratedBridge L2B L5A2C4A L5A2C4C L5A2C4D ChosenBase

variable {Gamma : NumericalSemigroup}

/-- The raw lattice coordinate obtained by adding `b` to `kappa1`.
It is deliberately distinct from its reduced coordinate. -/
def coherentKappa1RawAddB {B : Data Gamma} {e : Fin 3 ≃ Fin 3}
    (D : CoherentHerzogData B e) : ℕ × ℕ :=
  (c2 B e, cr13 D - 1)

/-- The raw lattice coordinate obtained by adding `c` to `kappa1`. -/
def coherentKappa1RawAddC {B : Data Gamma} {e : Fin 3 ≃ Fin 3}
    (D : CoherentHerzogData B e) : ℕ × ℕ :=
  (c2 B e - 1, cr13 D)

/-- The raw lattice coordinate obtained by adding both `b` and `c`. -/
def coherentKappa1RawAddBC {B : Data Gamma} {e : Fin 3 ≃ Fin 3}
    (D : CoherentHerzogData B e) : ℕ × ℕ :=
  (c2 B e, cr13 D)

/-- The canonical reduced coordinate of the raw `kappa1+b` point. -/
def coherentKappa1ReducedAddB (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (_D : CoherentHerzogData B e) : ℕ × ℕ :=
  (0, c3 B e - 1)

/-- The canonical reduced coordinate of the raw `kappa1+c` point. -/
def coherentKappa1ReducedAddC {B : Data Gamma} {e : Fin 3 ≃ Fin 3}
    (D : CoherentHerzogData B e) : ℕ × ℕ :=
  (cr32 D - 1, 0)

/-- The canonical reduced coordinate of the raw `kappa1+b+c` point. -/
def coherentKappa1ReducedAddBC {B : Data Gamma} {e : Fin 3 ≃ Fin 3}
    (D : CoherentHerzogData B e) : ℕ × ℕ :=
  (cr32 D, 0)

/-- Exact degree transport for raw addition of `b` at `kappa1`.
The reduced point carries `cr21` units in the `a` direction. -/
theorem coherent_kappa1_add_b_transport (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (n : ℕ) :
    gridDegree B e n (coherentKappa1RawAddB D).1 (coherentKappa1RawAddB D).2 =
      gridDegree B e (n + cr21 D) (coherentKappa1ReducedAddB B e D).1
        (coherentKappa1ReducedAddB B e D).2 := by
  have hr := coherent_relations B e D
  have hc := coherent_coefficients B e D
  have hp := coherent_coefficients_positive B e D
  have hs13 : cr13 D - 1 + 1 = cr13 D := Nat.sub_add_cancel hp.2.1
  have hc3sub : c3 B e - 1 = (cr13 D - 1) + cr23 D := by omega
  simp only [coherentKappa1RawAddB, coherentKappa1ReducedAddB, gridDegree,
    zero_mul, add_zero]
  calc
    n * weights B (e 0) + c2 B e * weights B (e 1) +
          (cr13 D - 1) * weights B (e 2) =
        n * weights B (e 0) +
          (cr21 D * weights B (e 0) + cr23 D * weights B (e 2)) +
          (cr13 D - 1) * weights B (e 2) := by rw [hr.2.1]
    _ = (n + cr21 D) * weights B (e 0) +
          (c3 B e - 1) * weights B (e 2) := by rw [hc3sub]; ring

/-- Exact degree transport for raw addition of `c` at `kappa1`.
The reduced point carries `c1` units in the `a` direction. -/
theorem coherent_kappa1_add_c_transport (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (n : ℕ) :
    gridDegree B e n (coherentKappa1RawAddC D).1 (coherentKappa1RawAddC D).2 =
      gridDegree B e (n + c1 B e) (coherentKappa1ReducedAddC D).1
        (coherentKappa1ReducedAddC D).2 := by
  have hr := coherent_relations B e D
  have hc := coherent_coefficients B e D
  have hp := coherent_coefficients_positive B e D
  have hs32 : cr32 D - 1 + 1 = cr32 D := Nat.sub_add_cancel hp.2.2.2.2.2
  have hc2pos : 0 < c2 B e := by omega
  have hs2 : c2 B e - 1 + 1 = c2 B e := Nat.sub_add_cancel hc2pos
  have hc2sub : c2 B e - 1 = cr12 D + (cr32 D - 1) := by omega
  simp only [coherentKappa1RawAddC, coherentKappa1ReducedAddC, gridDegree,
    zero_mul, add_zero]
  calc
    n * weights B (e 0) + (c2 B e - 1) * weights B (e 1) +
          cr13 D * weights B (e 2) =
        n * weights B (e 0) +
          (cr12 D * weights B (e 1) + cr13 D * weights B (e 2)) +
          (cr32 D - 1) * weights B (e 1) := by rw [hc2sub]; ring
    _ = n * weights B (e 0) + c1 B e * weights B (e 0) +
          (cr32 D - 1) * weights B (e 1) := by rw [hr.1]
    _ = (n + c1 B e) * weights B (e 0) +
          (cr32 D - 1) * weights B (e 1) := by ring

/-- Exact degree transport for raw addition of both `b` and `c` at `kappa1`.
The reduced point carries `c1` units in the `a` direction. -/
theorem coherent_kappa1_add_bc_transport (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (n : ℕ) :
    gridDegree B e n (coherentKappa1RawAddBC D).1 (coherentKappa1RawAddBC D).2 =
      gridDegree B e (n + c1 B e) (coherentKappa1ReducedAddBC D).1
        (coherentKappa1ReducedAddBC D).2 := by
  have hr := coherent_relations B e D
  have hc := coherent_coefficients B e D
  simp only [coherentKappa1RawAddBC, coherentKappa1ReducedAddBC, gridDegree,
    zero_mul, add_zero]
  calc
    n * weights B (e 0) + c2 B e * weights B (e 1) +
          cr13 D * weights B (e 2) =
        n * weights B (e 0) +
          (cr21 D * weights B (e 0) + cr23 D * weights B (e 2)) +
          cr13 D * weights B (e 2) := by rw [hr.2.1]
    _ = n * weights B (e 0) + cr21 D * weights B (e 0) +
          c3 B e * weights B (e 2) := by rw [hc.2.2]; ring
    _ = n * weights B (e 0) + cr21 D * weights B (e 0) +
          (cr31 D * weights B (e 0) + cr32 D * weights B (e 1)) := by
          rw [hr.2.2]
    _ = (n + c1 B e) * weights B (e 0) + cr32 D * weights B (e 1) := by
          rw [hc.1]; ring

/-- The `h3` transport used by the right edge of the square. -/
theorem coherent_Y3_add_c_transport (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (n : ℕ) :
    gridDegree B e n 0 (c3 B e) =
      gridDegree B e (n + cr31 D) (cr32 D) 0 := by
  have hr := coherent_relations B e D
  simp only [gridDegree, zero_mul, add_zero]
  nlinarith [hr.2.2]

/-- In the direct-`kappa1` gate (`Q1=0`), the actual base point of the
square has eta height zero. -/
theorem coherent_kappa1_eta_zero (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (hQ1 : coherentQ1 B e D = 0) :
    eta B e (coherentKappa1 B e D).1 (coherentKappa1 B e D).2 = 0 := by
  have hc := coherent_coefficients B e D
  have hp := coherent_coefficients_positive B e D
  have hm := eta_antitone_left B e (cr12 D) (cr13 D - 1) (cr32 D - 1)
  have hx : cr12 D + (cr32 D - 1) = c2 B e - 1 := by omega
  rw [hx] at hm
  change eta B e (c2 B e - 1) (cr13 D - 1) = 0
  change eta B e (cr12 D) (cr13 D - 1) = 0 at hQ1
  omega

/-- E3: the canonical/reduced local square.  The three successor entries
are read at their proved reduced coordinates, never at the raw additions. -/
theorem coherent_kappa1_local_square (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (hQ1 : coherentQ1 B e D = 0) :
    eta B e (coherentKappa1 B e D).1 (coherentKappa1 B e D).2 = 0 ∧
      eta B e (coherentKappa1ReducedAddB B e D).1
          (coherentKappa1ReducedAddB B e D).2 = coherentY3 B e D ∧
      eta B e (coherentKappa1ReducedAddC D).1
          (coherentKappa1ReducedAddC D).2 = coherentZ3minus B e D ∧
      eta B e (coherentKappa1ReducedAddBC D).1
          (coherentKappa1ReducedAddBC D).2 = coherentZ3 B e D := by
  refine ⟨coherent_kappa1_eta_zero B e D hQ1, ?_⟩
  simp [coherentKappa1ReducedAddB, coherentKappa1ReducedAddC,
    coherentKappa1ReducedAddBC, coherentY3, coherentZ3minus, coherentZ3]

private theorem coherent_Y3_le_cr21 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (hQ1 : coherentQ1 B e D = 0) :
    coherentY3 B e D ≤ cr21 D := by
  have hzero := coherent_kappa1_eta_zero B e D hQ1
  have hp := coherent_coefficients_positive B e D
  have hc := coherent_coefficients B e D
  have hc2pos : 0 < c2 B e := by omega
  have hs2 : c2 B e - 1 + 1 = c2 B e := Nat.sub_add_cancel hc2pos
  have hm := eta_antitone_left B e (c2 B e - 1) (cr13 D - 1) 1
  have hrawzero : eta B e (c2 B e) (cr13 D - 1) = 0 := by
    rw [hs2] at hm
    change eta B e (c2 B e - 1) (cr13 D - 1) = 0 at hzero
    omega
  have hk : gridDegree B e 0 (c2 B e) (cr13 D - 1) ∈ B.K :=
    (eta_eq_zero_iff B e _ _).mp hrawzero
  have ht : gridDegree B e 0 (c2 B e) (cr13 D - 1) =
      gridDegree B e (cr21 D) 0 (c3 B e - 1) := by
    simpa [coherentKappa1RawAddB, coherentKappa1ReducedAddB] using
      coherent_kappa1_add_b_transport B e D 0
  rw [ht] at hk
  have hle := eta_le_of_mem B e 0 (c3 B e - 1) (cr21 D) (by simpa using hk)
  simpa [coherentY3] using hle

private theorem coherent_Z3minus_le_c1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (hQ1 : coherentQ1 B e D = 0) :
    coherentZ3minus B e D ≤ c1 B e := by
  have hzero := coherent_kappa1_eta_zero B e D hQ1
  have hp := coherent_coefficients_positive B e D
  have hs13 : cr13 D - 1 + 1 = cr13 D := Nat.sub_add_cancel hp.2.1
  have hm := eta_antitone_right B e (c2 B e - 1) (cr13 D - 1) 1
  have hrawzero : eta B e (c2 B e - 1) (cr13 D) = 0 := by
    rw [hs13] at hm
    change eta B e (c2 B e - 1) (cr13 D - 1) = 0 at hzero
    omega
  have hk : gridDegree B e 0 (c2 B e - 1) (cr13 D) ∈ B.K :=
    (eta_eq_zero_iff B e _ _).mp hrawzero
  have ht : gridDegree B e 0 (c2 B e - 1) (cr13 D) =
      gridDegree B e (c1 B e) (cr32 D - 1) 0 := by
    simpa [coherentKappa1RawAddC, coherentKappa1ReducedAddC] using
      coherent_kappa1_add_c_transport B e D 0
  rw [ht] at hk
  have hle := eta_le_of_mem B e (cr32 D - 1) 0 (c1 B e) (by simpa using hk)
  simpa [coherentZ3minus] using hle

/-- First C-R2 inequality, obtained directly from eta antitonicity. -/
theorem coherent_Z3minus_ge_Z3 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    coherentZ3 B e D ≤ coherentZ3minus B e D := by
  have hp := coherent_coefficients_positive B e D
  have hs32 : cr32 D - 1 + 1 = cr32 D := Nat.sub_add_cancel hp.2.2.2.2.2
  have hm := eta_antitone_left B e (cr32 D - 1) 0 1
  rw [hs32] at hm
  simpa [coherentZ3, coherentZ3minus] using hm

/-- Second C-R2 inequality.  Starting at the actual `Y3` threshold, add one
`c`, transport through the coherent `h3` relation, and use eta minimality. -/
theorem coherent_Z3_le_cr31_add_Y3 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    coherentZ3 B e D ≤ cr31 D + coherentY3 B e D := by
  let Y := coherentY3 B e D
  have hk := eta_mem_K B e 0 (c3 B e - 1)
  have hadd := aperyTail_add_mem B.H_le hk (B.tailDegrees (e 2)).property
  have hc3pos : 0 < c3 B e := herzogC_positive B e 2
  have hs3 : c3 B e - 1 + 1 = c3 B e := Nat.sub_add_cancel hc3pos
  have hmul : c3 B e * weights B (e 2) =
      (c3 B e - 1) * weights B (e 2) + weights B (e 2) := by
    calc
      c3 B e * weights B (e 2) =
          ((c3 B e - 1) + 1) * weights B (e 2) := by rw [hs3]
      _ = (c3 B e - 1) * weights B (e 2) + weights B (e 2) := by
          rw [Nat.add_mul, one_mul]
  have hstep : gridDegree B e Y 0 (c3 B e) =
      gridDegree B e Y 0 (c3 B e - 1) + weights B (e 2) := by
    simp only [gridDegree, zero_mul, add_zero]
    rw [hmul]
    omega
  have hkraw : gridDegree B e Y 0 (c3 B e) ∈ B.K := by
    rw [hstep]
    change gridDegree B e (eta B e 0 (c3 B e - 1)) 0 (c3 B e - 1) +
      (B.tailDegrees (e 2)).val ∈ B.K
    exact hadd
  rw [coherent_Y3_add_c_transport B e D Y] at hkraw
  have hle := eta_le_of_mem B e (cr32 D) 0 (Y + cr31 D) hkraw
  simpa [Y, coherentY3, coherentZ3, Nat.add_comm] using hle

/-- The four raw carry quantities attached to the proved reduced transitions. -/
def coherentUKappa1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : ℕ :=
  cr21 D + eta B e (coherentKappa1 B e D).1 (coherentKappa1 B e D).2 -
    coherentY3 B e D

def coherentVKappa1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : ℕ :=
  c1 B e + eta B e (coherentKappa1 B e D).1 (coherentKappa1 B e D).2 -
    coherentZ3minus B e D

def coherentUKappa1AddC (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : ℕ :=
  coherentZ3minus B e D - coherentZ3 B e D

def coherentVKappa1AddB (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : ℕ :=
  cr31 D + coherentY3 B e D - coherentZ3 B e D

/-- E4: the exact four source stencil identities. -/
theorem coherent_kappa1_stencil (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (hQ1 : coherentQ1 B e D = 0) :
    coherentUKappa1 B e D = cr21 D - coherentY3 B e D ∧
      coherentVKappa1 B e D = c1 B e - coherentZ3minus B e D ∧
      coherentUKappa1AddC B e D = coherentZ3minus B e D - coherentZ3 B e D ∧
      coherentVKappa1AddB B e D =
        cr31 D + coherentY3 B e D - coherentZ3 B e D := by
  have hz := coherent_kappa1_eta_zero B e D hQ1
  have hy := coherent_Y3_le_cr21 B e D hQ1
  have hzm := coherent_Z3minus_le_c1 B e D hQ1
  unfold coherentUKappa1 coherentVKappa1 coherentUKappa1AddC coherentVKappa1AddB
  rw [hz]
  omega

/-- E5 raw nonnegativity, stated as the four pre-subtraction bounds actually
proved from `K` and eta. -/
theorem coherent_kappa1_raw_nonnegative (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (hQ1 : coherentQ1 B e D = 0) :
    coherentY3 B e D ≤ cr21 D ∧
      coherentZ3minus B e D ≤ c1 B e ∧
      coherentZ3 B e D ≤ coherentZ3minus B e D ∧
      coherentZ3 B e D ≤ cr31 D + coherentY3 B e D :=
  ⟨coherent_Y3_le_cr21 B e D hQ1,
    coherent_Z3minus_le_c1 B e D hQ1,
    coherent_Z3minus_ge_Z3 B e D,
    coherent_Z3_le_cr31_add_Y3 B e D⟩

/-- E6 paper-facing endpoint.  Its sole premise is the source branch gate
`Q1=0`; no square value, carry identity, coherence identity, or C-R2 bound is
accepted as input. -/
theorem coherent_kappa1_interface (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (hQ1 : coherentQ1 B e D = 0) :
    (eta B e (coherentKappa1 B e D).1 (coherentKappa1 B e D).2 = 0 ∧
      eta B e (coherentKappa1ReducedAddB B e D).1
          (coherentKappa1ReducedAddB B e D).2 = coherentY3 B e D ∧
      eta B e (coherentKappa1ReducedAddC D).1
          (coherentKappa1ReducedAddC D).2 = coherentZ3minus B e D ∧
      eta B e (coherentKappa1ReducedAddBC D).1
          (coherentKappa1ReducedAddBC D).2 = coherentZ3 B e D) ∧
    (coherentUKappa1 B e D = cr21 D - coherentY3 B e D ∧
      coherentVKappa1 B e D = c1 B e - coherentZ3minus B e D ∧
      coherentUKappa1AddC B e D = coherentZ3minus B e D - coherentZ3 B e D ∧
      coherentVKappa1AddB B e D = cr31 D + coherentY3 B e D - coherentZ3 B e D) ∧
    coherentZ3 B e D ≤ coherentZ3minus B e D ∧
    coherentZ3 B e D ≤ cr31 D + coherentY3 B e D :=
  ⟨coherent_kappa1_local_square B e D hQ1,
    coherent_kappa1_stencil B e D hQ1,
    coherent_Z3minus_ge_Z3 B e D,
    coherent_Z3_le_cr31_add_Y3 B e D⟩

end NS25Lean.L5A2C4E
