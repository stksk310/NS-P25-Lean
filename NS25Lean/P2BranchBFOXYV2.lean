import NS25Lean.P2BranchBFOXYAuthority
import NS25Lean.AperyConstruction
import NS25Lean.GenericLShapeCompleteness

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open ChosenBase L2B L5A1 L5A2B4AR1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Every normalized generator in the coherent Branch-B reindexing belongs to
the normalized three-generated semigroup. -/
theorem branchB_actual_normalizedWeight_mem
    (R : SectorBCriticalRoleBranchB P) (k : Fin 3) :
    L5A2B4AR3.normalizedWeight P.M.base (R.reindex k) ∈
      L5A2B4AR1.normalizedH P.M.base := by
  let B := P.M.base
  have hgen := (L5A2B4AR1.normalized_minimalThree B).1
  change L5A2B4AR3.normalizedWeight B (R.reindex k) ∈
    (L5A2B4AR1.normalizedH B).toAddSubmonoid
  rw [hgen]
  apply AddSubmonoid.subset_closure
  generalize R.reindex k = i
  fin_cases i <;>
    simp [L5A2B4AR3.normalizedWeight, L2B.weights,
      L5A2B4AR1.normalizedA, L5A2B4AR1.normalizedB,
      L5A2B4AR1.normalizedC]

/-- The distinguished first normalized generator in the coherent Branch-B
reindexing is an element of the normalized three-generated semigroup. -/
theorem branchB_actual_normalizedA_mem
    (R : SectorBCriticalRoleBranchB P) :
    normalizedA R ∈ L5A2B4AR1.normalizedH P.M.base :=
  branchB_actual_normalizedWeight_mem R 0

theorem branchB_actual_normalizedB_mem
    (R : SectorBCriticalRoleBranchB P) :
    normalizedB R ∈ L5A2B4AR1.normalizedH P.M.base :=
  branchB_actual_normalizedWeight_mem R 1

theorem branchB_actual_normalizedC_mem
    (R : SectorBCriticalRoleBranchB P) :
    normalizedC R ∈ L5A2B4AR1.normalizedH P.M.base :=
  branchB_actual_normalizedWeight_mem R 2

/-- The actual canonical return level `ell_* m`. -/
def branchBSelectedReturnLevel
    (_R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) : ℕ :=
  sectorBCanonicalReturnIndex P hB hs * normalizedM P.M.base

/-- The selected-return anchor `alpha_(ell_* m)` in the coherent `a`-residue
system.  This is deliberately distinct from the actual source `s`. -/
noncomputable def branchBSelectedReturnAnchor
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) : ℤ := by
  letI : NeZero (normalizedA R) :=
    ⟨(branchB_actual_normalizedA_pos R).ne'⟩
  exact (normalizedH P.M.base).asRelativeIdeal.aperyRepresentative
    (normalizedA R) (branchBSelectedReturnLevel R hB hs : ZMod (normalizedA R))

/-- Phase-A load-bearing packet.  It records the canonical selected depth,
the independent Apéry anchor, its positive `a`-depth, and the actual fact that
the old source is minimal in the selected individual return ideal. -/
structure ActualSelectedReturnAnchorV2
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) where
  ell : ℕ
  ell_eq : ell = sectorBCanonicalReturnIndex P hB hs
  ell_pos : 0 < ell
  ell_lt_principal : ell < actualPrincipalIndex P.M.base
  ell_min : ∀ k : ℕ,
    ReturnWitness (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s k → ell ≤ k
  n : ℕ
  n_eq : n = ell * normalizedM P.M.base
  n_not_mem : n ∉ normalizedH P.M.base
  source_minimal : (returnIdeal (normalizedH P.M.base) n).IsMinimalGenerator s
  beta : ℤ
  beta_eq : beta = branchBSelectedReturnAnchor R hB hs
  beta_mem : beta ∈ (normalizedH P.M.base).asRelativeIdeal
  beta_mod : (beta : ZMod (normalizedA R)) = (n : ZMod (normalizedA R))
  coordinate : ActualLShapeCoordinate R beta
  chart : ActualLShapeChart
  coordinate_in_chart :
    InActualLShapeChart R chart coordinate.i coordinate.j
  depth : ℕ
  depth_pos : 0 < depth
  anchor_eq : beta = n + normalizedA R * depth

noncomputable def branchB_actual_selected_return_anchor_v2
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    ActualSelectedReturnAnchorV2 R hB hs := by
  let ell := sectorBCanonicalReturnIndex P hB hs
  let n := ell * normalizedM P.M.base
  letI : NeZero (normalizedA R) :=
    ⟨(branchB_actual_normalizedA_pos R).ne'⟩
  let beta := branchBSelectedReturnAnchor R hB hs
  have hreturn := sectorBCanonicalReturnIndex_spec P hB hs
  have hn_not_mem : n ∉ normalizedH P.M.base := by
    intro hn
    have hqle := principalIndex_min (normalizedH P.M.base)
      (normalizedM P.M.base) P.M.base.q_positive hreturn.1 hn
    exact (Nat.not_le_of_gt hreturn.2.1) hqle
  have hbeta_mem : beta ∈ (normalizedH P.M.base).asRelativeIdeal := by
    dsimp [beta, branchBSelectedReturnAnchor]
    exact (normalizedH P.M.base).asRelativeIdeal.aperyRepresentative_mem
      (normalizedA R) (n : ZMod (normalizedA R))
  have hbeta_mod : (beta : ZMod (normalizedA R)) =
      (n : ZMod (normalizedA R)) := by
    dsimp [beta, branchBSelectedReturnAnchor]
    exact (normalizedH P.M.base).asRelativeIdeal.aperyRepresentative_mod
      (normalizedA R) (n : ZMod (normalizedA R))
  have hbeta_mod_int : (beta : ZMod (normalizedA R)) =
      ((n : ℤ) : ZMod (normalizedA R)) := by
    simpa using hbeta_mod
  have hn_lt_beta : (n : ℤ) < beta := by
    by_contra hnot
    have hbeta_le : beta ≤ (n : ℤ) := le_of_not_gt hnot
    obtain ⟨k, hk⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
      (normalizedA R) hbeta_le hbeta_mod_int.symm
    rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hbeta_mem
    obtain ⟨b, hbH, hbeta_b⟩ := hbeta_mem
    have hn_eq : n = b + normalizedA R * k := by
      exact_mod_cast (show (n : ℤ) = (b : ℤ) + (normalizedA R * k : ℕ) by
        rw [hk, hbeta_b]
        norm_num)
    have hakH : normalizedA R * k ∈ normalizedH P.M.base := by
      simpa [nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedA_mem R) k
    apply hn_not_mem
    rw [hn_eq]
    exact (normalizedH P.M.base).add_mem hbH hakH
  let hdepthExists := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
    (normalizedA R) (le_of_lt hn_lt_beta) hbeta_mod_int
  let depth := Classical.choose hdepthExists
  have hdepth := Classical.choose_spec hdepthExists
  have hdepth_pos : 0 < depth := by
    by_contra hnot
    have hd0 : depth = 0 := Nat.eq_zero_of_not_pos hnot
    change beta = (n : ℤ) + (normalizedA R : ℤ) * (depth : ℤ) at hdepth
    rw [hd0, Nat.cast_zero, mul_zero, add_zero] at hdepth
    omega
  let coordinate := branchB_actual_lShape_coordinate R beta
  let chart := branchB_actual_lShape_chart R coordinate.in_lShape
  exact {
    ell := ell
    ell_eq := rfl
    ell_pos := hreturn.1
    ell_lt_principal := hreturn.2.1
    ell_min := fun k hk => canonicalReturnIndex_min
      (sectorB_branchBirth_isPrefixSource P hB hs) hk
    n := n
    n_eq := rfl
    n_not_mem := hn_not_mem
    source_minimal := hreturn.2.2
    beta := beta
    beta_eq := rfl
    beta_mem := hbeta_mem
    beta_mod := hbeta_mod
    coordinate := coordinate
    chart := chart
    coordinate_in_chart := branchB_actual_lShape_chart_spec R coordinate.in_lShape
    depth := depth
    depth_pos := hdepth_pos
    anchor_eq := hdepth
  }

/-- The selected Apéry anchor is represented by the bottom of its actual
Herzog L-shape column.  The proof reduces an arbitrary normalized
factorization to the L-shape and then uses Apéry minimality; it does not
identify the anchor with the original branch-birth source. -/
theorem branchB_selected_return_anchor_level_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.level = 0 := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := C.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := C.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := C.normalized_relations
  have hbetaMem := A.beta_mem
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hbetaMem
  obtain ⟨betaNat, hbetaNatH, hbetaNatEq⟩ := hbetaMem
  obtain ⟨x, y, z, hfactor⟩ :=
    branchB_exists_reindexed_normalized_factorization R hbetaNatH
  obtain ⟨i, j, k, hdomain, hreduce⟩ := GenericLShape.exists_reduction
    (normalizedA R) (normalizedB R) (normalizedC R)
    (L5A2B4AR4R2B.c1 R) (L5A2B4AR4R2B.c2 R)
    (L5A2B4AR4R2B.c3 R) (pH R) (qH R) (zH R) (vH R)
    (uH R) (wH R) (branchB_actual_normalizedA_pos R)
    (criticalExponent_spec P.M.base (R.reindex 0)).1 hu hw
    hs2 hs3 hrel1 hrel2 hrel3 y z
  have hshape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      (i : ℤ) (j : ℤ) := by
    rcases hdomain with ⟨hi, hj, hcorner⟩
    refine ⟨by positivity, by positivity, ?_, ?_, ?_⟩
    · exact_mod_cast (show i < pH R + zH R by simpa [← hs2] using hi)
    · exact_mod_cast (show j < qH R + vH R by simpa [← hs3] using hj)
    · rcases hcorner with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
  have hterminalNat : betaNat =
      (x + k) * normalizedA R + i * normalizedB R + j * normalizedC R := by
    nlinarith only [hfactor, hreduce]
  have hterminal : A.beta =
      ((x + k : ℕ) : ℤ) * (normalizedA R : ℤ) +
        (i : ℤ) * (normalizedB R : ℤ) +
          (j : ℤ) * (normalizedC R : ℤ) := by
    calc
      A.beta = (betaNat : ℤ) := hbetaNatEq
      _ = (((x + k) * normalizedA R + i * normalizedB R +
          j * normalizedC R : ℕ) : ℤ) := by exact_mod_cast hterminalNat
      _ = _ := by push_cast; ring
  have hmod : Int.ModEq (normalizedA R)
      ((i : ℤ) * normalizedB R + (j : ℤ) * normalizedC R) A.beta := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(x + k : ℤ), ?_⟩
    push_cast at ⊢
    nlinarith
  obtain ⟨hi, hj⟩ := A.coordinate.pair_unique (i : ℤ) (j : ℤ) hshape hmod
  have hlevel : A.coordinate.level = (x + k : ℕ) := by
    rw [hi, hj] at hterminal
    exact (A.coordinate.level_unique (x + k : ℕ) hterminal).symm
  let tail := i * normalizedB R + j * normalizedC R
  have htailH : tail ∈ normalizedH P.M.base := by
    have hiH := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
      (branchB_actual_normalizedB_mem R) i
    have hjH := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
      (branchB_actual_normalizedC_mem R) j
    simpa [tail, nsmul_eq_mul] using (normalizedH P.M.base).add_mem hiH hjH
  have htailMem : (tail : ℤ) ∈ (normalizedH P.M.base).asRelativeIdeal :=
    ⟨tail, htailH, rfl⟩
  have htailModBeta :
      ((tail : ℤ) : ZMod (normalizedA R)) =
        (A.beta : ZMod (normalizedA R)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).2 (by
      simpa [tail] using hmod)
  have htailModN :
      ((tail : ℤ) : ZMod (normalizedA R)) =
        (A.n : ZMod (normalizedA R)) :=
    htailModBeta.trans A.beta_mod
  have hbetaLe : A.beta ≤ (tail : ℤ) := by
    letI : NeZero (normalizedA R) :=
      ⟨(branchB_actual_normalizedA_pos R).ne'⟩
    rw [A.beta_eq]
    exact (normalizedH P.M.base).asRelativeIdeal.aperyRepresentative_le
      (normalizedA R) (A.n : ZMod (normalizedA R)) htailMem htailModN
  have ha : (0 : ℤ) < normalizedA R := by
    exact_mod_cast branchB_actual_normalizedA_pos R
  dsimp [tail] at hbetaLe
  rw [hi, hj] at hbetaLe
  let tailZ : ℤ :=
    A.coordinate.i * (normalizedB R : ℤ) +
      A.coordinate.j * (normalizedC R : ℤ)
  change A.beta ≤ tailZ at hbetaLe
  rw [hi, hj] at hterminal
  have hterminal' : A.beta =
      ((x + k : ℕ) : ℤ) * (normalizedA R : ℤ) + tailZ := by
    simpa only [tailZ, add_assoc] using hterminal
  have hxk : x + k = 0 := by
    by_contra hne
    have hxkpos : (0 : ℤ) < (x + k : ℕ) := by
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hprod : (0 : ℤ) < ((x + k : ℕ) : ℤ) * normalizedA R :=
      mul_pos hxkpos ha
    have hstrict : tailZ < A.beta := by
      nlinarith only [hterminal', hprod]
    exact (not_lt_of_ge hbetaLe) hstrict
  rw [hlevel, hxk]
  rfl

/-- Strongest Phase-B checkpoint before the positive-axis and depth-bound
refinement: the selected anchor has natural L-shape coordinates, lies at level
zero, satisfies the exact tail equation, retains its broad chart, and retains
the independently constructed positive return depth. -/
theorem branchB_actual_selected_return_anchor_bottom_v2
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    ∃ i j : ℕ,
      A.coordinate.i = (i : ℤ) ∧
      A.coordinate.j = (j : ℤ) ∧
      A.coordinate.level = 0 ∧
      A.beta = (i : ℤ) * normalizedB R + (j : ℤ) * normalizedC R ∧
      L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) (i : ℤ) (j : ℤ) ∧
      InActualLShapeChart R A.chart (i : ℤ) (j : ℤ) ∧
      0 < A.depth ∧
      A.beta = A.n + normalizedA R * A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  rcases A.coordinate.in_lShape with ⟨hi0, hj0, hibound, hjbound, hcorner⟩
  let i := A.coordinate.i.toNat
  let j := A.coordinate.j.toNat
  have hi : (i : ℤ) = A.coordinate.i := Int.toNat_of_nonneg hi0
  have hj : (j : ℤ) = A.coordinate.j := Int.toNat_of_nonneg hj0
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hbeta := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add, ← hi, ← hj] at hbeta
  refine ⟨i, j, hi.symm, hj.symm, hlevel, hbeta,
    ⟨by positivity, by positivity, ?_, ?_, ?_⟩, ?_, A.depth_pos, A.anchor_eq⟩
  · simpa [hi] using hibound
  · simpa [hj] using hjbound
  · simpa [hi, hj] using hcorner
  · simpa [hi, hj] using A.coordinate_in_chart

/-- Exact reduction of the Phase-B2 positivity problem to the two genuine
axis obstructions.  The alternatives retain the selected-return equation,
the positive coordinate on the surviving axis, and the sharp L-shape bound.
No generic L-shape argument can eliminate either of the last two cases. -/
theorem branchB_selected_return_anchor_positive_or_axis_obstruction
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    (1 ≤ A.coordinate.i ∧ 1 ≤ A.coordinate.j) ∨
      (A.coordinate.i = 0 ∧
        1 ≤ A.coordinate.j ∧ A.coordinate.j < qH R + vH R ∧
        A.beta = A.coordinate.j * normalizedC R ∧
        (A.n : ℤ) + normalizedA R * A.depth =
          A.coordinate.j * normalizedC R) ∨
      (A.coordinate.j = 0 ∧
        1 ≤ A.coordinate.i ∧ A.coordinate.i < pH R + zH R ∧
        A.beta = A.coordinate.i * normalizedB R ∧
        (A.n : ℤ) + normalizedA R * A.depth =
          A.coordinate.i * normalizedB R) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hbeta := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add] at hbeta
  have hi0 := A.coordinate.in_lShape.1
  have hj0 := A.coordinate.in_lShape.2.1
  have hibound := A.coordinate.in_lShape.2.2.1
  have hjbound := A.coordinate.in_lShape.2.2.2.1
  have hnpos : 0 < A.n := by
    rw [A.n_eq]
    exact Nat.mul_pos A.ell_pos P.M.base.q_positive
  have hbetaPos : (0 : ℤ) < A.beta := by
    rw [A.anchor_eq]
    have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
    positivity
  by_cases hi : 1 ≤ A.coordinate.i
  · by_cases hj : 1 ≤ A.coordinate.j
    · exact Or.inl ⟨hi, hj⟩
    · have hjz : A.coordinate.j = 0 := by omega
      right
      right
      refine ⟨hjz, hi, hibound, ?_, ?_⟩
      · simpa [hjz] using hbeta
      · calc
          (A.n : ℤ) + normalizedA R * A.depth = A.beta := A.anchor_eq.symm
          _ = A.coordinate.i * normalizedB R := by simpa [hjz] using hbeta
  · have hiz : A.coordinate.i = 0 := by omega
    have hj : 1 ≤ A.coordinate.j := by
      by_contra hnot
      have hjz : A.coordinate.j = 0 := by omega
      rw [hiz, hjz] at hbeta
      norm_num at hbeta
      omega
    right
    left
    refine ⟨hiz, hj, hjbound, ?_, ?_⟩
    · simpa [hiz] using hbeta
    · calc
        (A.n : ℤ) + normalizedA R * A.depth = A.beta := A.anchor_eq.symm
        _ = A.coordinate.j * normalizedC R := by simpa [hiz] using hbeta

end NS25Lean.L5A2B4AR5B
