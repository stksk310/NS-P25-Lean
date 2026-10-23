import NS25Lean.P2BranchBHighAxisCUTargetExclusion

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2B4AR4R2B L5A2C4C L5A2C4H L5A2C4OR3
open L5A2C4OR1 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-! B66R: the direct B-tail clamp.  The frozen B65 module is used only
through its public interface. -/

/-- A nonterminal coherent Herzog reduction removes a positive multiple of
the local `a` generator.  This is the positivity information deliberately
not retained by the older existential reduction interface. -/
theorem branchB_coherent_exists_positive_reduction_of_not_domain
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : L5A2C4D.CoherentHerzogData B e) (x y : ℕ)
    (hnot : ¬ L5A2C4OR5.HerzogLShapeDomain D x y) :
    ∃ i j k : ℕ,
      L5A2C4OR5.HerzogLShapeDomain D i j ∧ 0 < k ∧
        x * routingB B e + y * routingC B e =
          i * routingB B e + j * routingC B e + k * routingA B e := by
  have hp := L5A2C4D.coherent_coefficients_positive B e D
  have hs := L5A2C4D.coherent_coefficients B e D
  have hr := L5A2C4OR5.coherent_normalized_relations B e D
  by_cases hx : L5A2C4A.c2 B e ≤ x
  · let x' := x - L5A2C4A.c2 B e
    let y' := y + L5A2C4D.cr23 D
    obtain ⟨i, j, k, hdom, heq⟩ :=
      L5A2C4OR6.coherent_exists_reduction B e D x' y'
    refine ⟨i, j, k + L5A2C4D.cr21 D, hdom, by omega, ?_⟩
    have hcancel : x' + L5A2C4A.c2 B e = x := Nat.sub_add_cancel hx
    have hrel := hr.2.1
    calc
      x * routingB B e + y * routingC B e =
          x' * routingB B e + y' * routingC B e +
            L5A2C4D.cr21 D * routingA B e := by
              rw [← hcancel]
              dsimp [y']
              rw [add_mul, hrel]
              ring
      _ = i * routingB B e + j * routingC B e +
          (k + L5A2C4D.cr21 D) * routingA B e := by rw [heq]; ring
  · by_cases hy : L5A2C4A.c3 B e ≤ y
    · let x' := x + L5A2C4D.cr32 D
      let y' := y - L5A2C4A.c3 B e
      obtain ⟨i, j, k, hdom, heq⟩ :=
        L5A2C4OR6.coherent_exists_reduction B e D x' y'
      refine ⟨i, j, k + L5A2C4D.cr31 D, hdom, by omega, ?_⟩
      have hcancel : y' + L5A2C4A.c3 B e = y := Nat.sub_add_cancel hy
      have hrel := hr.2.2
      calc
        x * routingB B e + y * routingC B e =
            x' * routingB B e + y' * routingC B e +
              L5A2C4D.cr31 D * routingA B e := by
                rw [← hcancel]
                dsimp [x']
                rw [add_mul, hrel]
                ring
        _ = i * routingB B e + j * routingC B e +
            (k + L5A2C4D.cr31 D) * routingA B e := by rw [heq]; ring
    · by_cases hcorner : L5A2C4D.cr12 D ≤ x ∧ L5A2C4D.cr13 D ≤ y
      · let x' := x - L5A2C4D.cr12 D
        let y' := y - L5A2C4D.cr13 D
        obtain ⟨i, j, k, hdom, heq⟩ :=
          L5A2C4OR6.coherent_exists_reduction B e D x' y'
        refine ⟨i, j, k + L5A2C4A.c1 B e, hdom,
          by exact Nat.add_pos_right k (criticalExponent_spec B (e 0)).1, ?_⟩
        have hxcancel : x' + L5A2C4D.cr12 D = x := Nat.sub_add_cancel hcorner.1
        have hycancel : y' + L5A2C4D.cr13 D = y := Nat.sub_add_cancel hcorner.2
        have hrel := hr.1
        calc
          x * routingB B e + y * routingC B e =
              x' * routingB B e + y' * routingC B e +
                L5A2C4A.c1 B e * routingA B e := by
                  rw [← hxcancel, ← hycancel]
                  rw [add_mul, add_mul, hrel]
                  ring
          _ = i * routingB B e + j * routingC B e +
              (k + L5A2C4A.c1 B e) * routingA B e := by rw [heq]; ring
      · exfalso
        apply hnot
        exact ⟨lt_of_not_ge hx, lt_of_not_ge hy, by omega⟩

/-- Every ambient Apéry representative has a coherent canonical L-shape
coordinate. -/
theorem branchB_physicalAlpha_canonical_coordinates
    (R : SectorBCriticalRoleBranchB P)
    (s : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    ∃ I J : ℕ,
      L5A2C4OR5.HerzogLShapeDomain
          (branchB_inactive_coherentHerzogData R) I J ∧
        gridResidue P.M.base (branchBInactiveReindex R) I J = s ∧
        physicalAlpha P.M.base (branchBInactiveReindex R) s =
          normalizedGrid P.M.base (branchBInactiveReindex R) 0 I J := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let alpha := physicalAlpha B e s
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have halphaMem : alpha ∈ (routingH B e).asRelativeIdeal := by
    dsimp [alpha, physicalAlpha]
    exact (routingH B e).asRelativeIdeal.aperyRepresentative_mem a s
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at halphaMem
  obtain ⟨n, hnH, hnalpha⟩ := halphaMem
  obtain ⟨x, y, z, hnfac⟩ := L5A2C4OR6.routingH_factorization B e hnH
  obtain ⟨I, J, q, hdom, hreduce⟩ :=
    L5A2C4OR6.coherent_exists_reduction B e D y z
  have hnterminal : n = I * b + J * c + (x + q) * a := by
    calc
      n = x * a + y * b + z * c := hnfac
      _ = x * a + (y * b + z * c) := by ring
      _ = x * a + (I * b + J * c + q * a) := by rw [hreduce]
      _ = I * b + J * c + (x + q) * a := by ring
  have hnResidue : (n : ZMod a) = s := by
    have hm := (routingH B e).asRelativeIdeal.aperyRepresentative_mod a s
    change (alpha : ZMod a) = s at hm
    rw [hnalpha] at hm
    exact_mod_cast hm
  have hres : gridResidue B e I J = s := by
    simp only [gridResidue]
    calc
      (I : ZMod a) * routingB B e + (J : ZMod a) * routingC B e =
          ((I * b + J * c : ℕ) : ZMod a) := by push_cast; rfl
      _ = (n : ZMod a) := by rw [hnterminal]; push_cast; simp
      _ = s := hnResidue
  have hcanon := L5A2C4OR6.herzogLShapeCanonicality B e D I J hdom
  have halpha : physicalAlpha B e s = normalizedGrid B e 0 I J := by
    rw [← hres]
    exact hcanon.symm
  exact ⟨I, J, hdom, hres, halpha⟩

private theorem branchB_apery_eq_of_predecessor_excluded
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (n : ℕ)
    (hn : n ∈ routingH B e)
    (hpred : (n : ℤ) - routingA B e ∉ (routingH B e).asRelativeIdeal) :
    physicalAlpha B e (n : ZMod (routingA B e)) = n := by
  let a := routingA B e
  let H := routingH B e
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hmem : (n : ℤ) ∈ H.asRelativeIdeal := by
    rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨n, hn, rfl⟩
  have hle := H.asRelativeIdeal.aperyRepresentative_le a (n : ZMod a) hmem (by simp)
  obtain ⟨k, hk⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq a hle
    (by rw [H.asRelativeIdeal.aperyRepresentative_mod]; simp)
  cases k with
  | zero => simpa [physicalAlpha, H, a] using hk.symm
  | succ k =>
    have hak : a * k ∈ H := by
      change a * k ∈ generatedThree a (routingB B e) (routingC B e)
      exact (mem_generatedThree_iff _ _ _ _).2 ⟨k, 0, 0, by ring⟩
    have hadd := H.asRelativeIdeal.add_mem_nat
      (H.asRelativeIdeal.aperyRepresentative_mem a (n : ZMod a)) hak
    apply (hpred ?_).elim
    have heq : (n : ℤ) - a = H.asRelativeIdeal.aperyRepresentative a (n : ZMod a) + (a * k : ℕ) := by
      push_cast at hk ⊢
      nlinarith only [hk]
    change (n : ℤ) - a ∈ H.asRelativeIdeal
    rw [heq]
    exact hadd

/-- R1: the principal element and its complementary Apéry summand add
without a Herzog reduction at the inner notch. -/
theorem branchB_high_axisC_principal_coordinate_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let Q := actualPrincipalIndex B
    ∃ P0 T0 : ℕ,
      Q * routingM B e = P0 * routingB B e + T0 * routingC B e ∧
        P0 < r31 R ∧ T0 < r32 R := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let N := actualPrincipalIndex B * routingM B e
  let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hn : N ∈ routingH B e := by
    rw [branchBRoutingH_eq_normalizedH R]
    exact (actualPrincipalIndex_spec B).2
  have hpred := branchB_actualZeroEdgeBirth_axisC_high_seam_principal_routingA_predecessor_excluded
    R hB x hsx hbirth haxis
  have hprincipal := branchB_apery_eq_of_predecessor_excluded B e N hn hpred
  obtain ⟨P0, T0, hd0, hr0, hv0⟩ :=
    branchB_physicalAlpha_canonical_coordinates R (N : ZMod a)
  obtain ⟨P1, T1, hd1, hr1, hv1⟩ :=
    branchB_physicalAlpha_canonical_coordinates R (A0 - (N : ZMod a))
  have hN : N = P0 * b + T0 * c := by
    rw [hprincipal] at hv0
    simp only [normalizedGrid, zero_mul, zero_add] at hv0
    exact_mod_cast hv0
  have cp := L5A2C4D.coherent_coefficients_positive B e D
  have cs := L5A2C4D.coherent_coefficients B e D
  have hc := branchB_inactive_coherent_coefficients R
  have hp : 0 < r31 R := hc.1 ▸ cp.1
  have hq : 0 < r32 R := hc.2.1 ▸ cp.2.1
  have hdA : HerzogLShapeDomain D (r31 R - 1) (r32 R - 1) := by
    change _ < _ ∧ _ < _ ∧ (_ < _ ∨ _ < _)
    rw [cs.2.1, cs.2.2, hc.1, hc.2.1]
    omega
  have hvA := herzogLShapeCanonicality B e D _ _ hdA
  have heq := branchB_actualZeroEdgeBirth_axisC_high_seam_principal_inner_notch_apery_eq
    R hB x hsx hbirth haxis
  change (N : ℤ) + physicalAlpha B e (A0 - (N : ZMod a)) = physicalAlpha B e A0 at heq
  have hsum : (P0 + P1) * b + (T0 + T1) * c =
      (r31 R - 1) * b + (r32 R - 1) * c := by
    rw [hv1, ← hvA] at heq
    simp only [normalizedGrid, zero_mul, zero_add] at heq
    have hNi : (N : ℤ) = (P0 * b + T0 * c : ℕ) := by rw [hN]
    rw [hNi] at heq
    have heqNat : P0 * b + T0 * c + (P1 * b + T1 * c) =
        (r31 R - 1) * b + (r32 R - 1) * c := by exact_mod_cast heq
    calc
      _ = P0 * b + T0 * c + (P1 * b + T1 * c) := by ring
      _ = _ := heqNat
  have hdSum : HerzogLShapeDomain D (P0 + P1) (T0 + T1) := by
    by_contra hnot
    obtain ⟨I, J, K, hd, hk, hred⟩ :=
      branchB_coherent_exists_positive_reduction_of_not_domain B e D _ _ hnot
    have hm : (K - 1) * a + I * b + J * c ∈ routingH B e := by
      change _ ∈ generatedThree a b c
      exact (mem_generatedThree_iff _ _ _ _).2 ⟨K - 1, I, J, rfl⟩
    have hbad : physicalAlpha B e A0 - a ∈ (routingH B e).asRelativeIdeal := by
      rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      refine ⟨(K - 1) * a + I * b + J * c, hm, ?_⟩
      rw [← hvA]
      have hgrid : normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) =
          (r31 R - 1) * b + (r32 R - 1) * c := by
        simp only [normalizedGrid, zero_mul, zero_add]
        rfl
      rw [hgrid]
      change (((r31 R - 1) * b + (r32 R - 1) * c : ℕ) : ℤ) - a =
        (((K - 1) * a + I * b + J * c : ℕ) : ℤ)
      have hvalue : (r31 R - 1) * b + (r32 R - 1) * c = I * b + J * c + K * a :=
        hsum.symm.trans hred
      have hki : (K : ℤ) - 1 = ((K - 1 : ℕ) : ℤ) := by omega
      have hvaluei := congrArg (fun n : ℕ => (n : ℤ)) hvalue
      push_cast at hvaluei ⊢
      rw [← hki]
      nlinarith only [hvaluei]
    exact ((routingH B e).asRelativeIdeal.aperyRepresentative_sub_modulus_not_mem a A0) hbad
  have hmod : Int.ModEq a
      (((P0 + P1 : ℕ) : ℤ) * b + ((T0 + T1 : ℕ) : ℤ) * c)
      (((r31 R - 1 : ℕ) : ℤ) * b + ((r32 R - 1 : ℕ) : ℤ) * c) := by
    have hi := congrArg (fun n : ℕ => (n : ℤ)) hsum
    push_cast at hi ⊢
    rw [hi]
  have hu := GenericLShape.modEq_unique a b c
    (L5A2C4A.c2 B e) (L5A2C4A.c3 B e)
    (L5A2C4D.cr12 D) (L5A2C4D.cr13 D) (L5A2C4D.cr32 D) (L5A2C4D.cr23 D)
    cp.1 cp.2.1 cp.2.2.2.2.2 cp.2.2.2.1 cs.2.1 cs.2.2
    (coherent_second_minimality B e D) (coherent_third_minimality B e D)
    (coherent_uniqueZeroInLShape B e D)
    (inLShape_of_herzogDomain B e D hdSum)
    (inLShape_of_herzogDomain B e D hdA) hmod
  have hi : P0 + P1 = r31 R - 1 := by exact_mod_cast hu.1
  have hj : T0 + T1 = r32 R - 1 := by exact_mod_cast hu.2
  exact ⟨P0, T0, hN, by omega, by omega⟩

private theorem branchB_r2_prefix_candidate_positive
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R)))
    (hheight : 0 < branchBPrefixHeight R x hsx r)
    {k : ℕ} (hk : 0 < k) (hklt : k < actualPrincipalIndex P.M.base) :
    0 < rawCandidate P.M.base (branchBInactiveReindex R) k r := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let H := routingH B e
  let Iminus := branchBActualPrefixIdeal R x hsx
  by_contra hnot
  have hcand : rawCandidate B e k r ≤ 0 := le_of_not_gt hnot
  have hsub := (rawCandidate_threshold B e r hk 0).2 hcand
  have hsub' : physicalAlpha B e r - k * routingM B e ∈ H.asRelativeIdeal := by
    simpa [H] using hsub
  have halphaH : physicalAlpha B e r ∈ H.asRelativeIdeal :=
    H.asRelativeIdeal.aperyRepresentative_mem (routingA B e) r
  have hreturn : physicalAlpha B e r ∈ returnIdeal H (k * routingM B e) := by
    rw [mem_returnIdeal_iff]
    exact ⟨halphaH, hsub'⟩
  have hpref : physicalAlpha B e r ∈ Iminus := by
    change ∃ ell : ℕ, 0 < ell ∧ ell < actualPrincipalIndex B ∧
      physicalAlpha B e r ∈ returnIdeal H (ell * normalizedM B)
    refine ⟨k, hk, hklt, ?_⟩
    simpa [routingM, normalizedM, B, e] using hreturn
  have hle := Iminus.aperyRepresentative_le (routingA B e) r hpref (by
    change ((physicalAlpha B e r : ℤ) : ZMod (routingA B e)) = r
    exact H.asRelativeIdeal.aperyRepresentative_mod (routingA B e) r)
  have hambient := branchB_prefix_alpha_le R x hsx r
  have heq : Iminus.aperyRepresentative (routingA B e) r =
      branchBPrefixAlpha R r := le_antisymm hle hambient
  have hdict := branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx r
  change Iminus.aperyRepresentative (routingA B e) r =
    branchBPrefixAlpha R r +
      (routingA B e : ℤ) * branchBPrefixHeight R x hsx r at hdict
  rw [heq] at hdict
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hzero : branchBPrefixHeight R x hsx r = 0 := by
    have : (routingA B e : ℤ) * branchBPrefixHeight R x hsx r = 0 := by linarith
    exact_mod_cast (mul_eq_zero.mp this |>.resolve_left (ne_of_gt ha))
  exact (Nat.ne_of_gt hheight) hzero

/-- R2: the complementary strict-prefix candidate prevents the principal
B-coordinate plus selected depth from lying below the inner notch. -/
theorem branchB_high_axisC_complementary_principal_coordinate_bound
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (P0 T0 : ℕ)
    (hcoord :
      actualPrincipalIndex P.M.base *
          routingM P.M.base (branchBInactiveReindex R) =
        P0 * routingB P.M.base (branchBInactiveReindex R) +
        T0 * routingC P.M.base (branchBInactiveReindex R))
    (hP0 : P0 < r31 R) (hT0 : T0 < r32 R) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    r31 R ≤ P0 + S.depth := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let Q := actualPrincipalIndex B
  let k := Q - S.ell
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let m := routingM B e
  let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change r31 R ≤ P0 + S.depth
  by_contra hnot
  have hsmall : P0 + S.depth < r31 R := lt_of_not_ge hnot
  have hellpos := S.ell_pos
  have helllt : S.ell < Q := S.ell_lt_principal
  have hkpos : 0 < k := by dsimp only [k]; omega
  have hklt : k < Q := by dsimp only [k]; omega
  have hQsplit : Q = k + S.ell := by dsimp only [k]; omega
  let I := r31 R - 1 - P0 - S.depth
  let J := r32 R - 1 - T0
  have hI : I + P0 + S.depth = r31 R - 1 := by dsimp only [I]; omega
  have hJ : J + T0 = r32 R - 1 := by dsimp only [J]; omega
  have cp := L5A2C4D.coherent_coefficients_positive B e D
  have cs := L5A2C4D.coherent_coefficients B e D
  have hc := branchB_inactive_coherent_coefficients R
  have hp : 0 < r31 R := hc.1 ▸ cp.1
  have hq : 0 < r32 R := hc.2.1 ▸ cp.2.1
  have hdA : HerzogLShapeDomain D (r31 R - 1) (r32 R - 1) := by
    change _ < _ ∧ _ < _ ∧ (_ < _ ∨ _ < _)
    rw [cs.2.1, cs.2.2, hc.1, hc.2.1]
    omega
  have hdIJ : HerzogLShapeDomain D I J := by
    change _ < _ ∧ _ < _ ∧ (_ < _ ∨ _ < _)
    rw [cs.2.1, cs.2.2, hc.1, hc.2.1]
    omega
  have hAeq : a = normalizedC R := branchB_inactive_routingA_eq_normalizedC R
  have hBeq : b = normalizedA R := branchB_inactive_routingB_eq_normalizedA R
  have hMeq : m = normalizedM B := by simp [m, routingM]
  have hn : S.n = S.ell * m := by rw [S.n_eq, hMeq]
  change S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
    S.coordinate.j < qH R + vH R ∧ S.beta = S.coordinate.j * normalizedC R ∧
    (S.n : ℤ) + normalizedA R * S.depth = S.coordinate.j * normalizedC R at haxis
  have hjnonneg : (0 : ℤ) ≤ S.coordinate.j := by omega
  have hsel : (S.ell : ℤ) * m + (S.depth : ℤ) * b = S.coordinate.j * a := by
    have h := haxis.2.2.2.2
    rw [hn, ← hBeq, ← hAeq] at h
    push_cast at h
    nlinarith only [h]
  have hcoordi : (Q : ℤ) * m = (P0 : ℤ) * b + (T0 : ℤ) * c := by
    exact_mod_cast hcoord
  have hQi : (Q : ℤ) = (k : ℤ) + S.ell := by exact_mod_cast hQsplit
  have hIi : (I : ℤ) + P0 + S.depth = ((r31 R - 1 : ℕ) : ℤ) := by exact_mod_cast hI
  have hJi : (J : ℤ) + T0 = ((r32 R - 1 : ℕ) : ℤ) := by exact_mod_cast hJ
  have hbalance : ((k * m : ℕ) : ℤ) + ((I * b + J * c : ℕ) : ℤ) =
      (((r31 R - 1) * b + (r32 R - 1) * c : ℕ) : ℤ) - S.coordinate.j * a := by
    push_cast
    nlinarith only [hsel, hcoordi, hQi, hIi, hJi]
  have hres : A0 - (k * m : ZMod a) = gridResidue B e I J := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod a)) hbalance
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, mul_zero, sub_zero] at hcast
    change ((r31 R - 1 : ℕ) : ZMod a) * b + ((r32 R - 1 : ℕ) : ZMod a) * c -
      (k * m : ZMod a) = (I : ZMod a) * b + (J : ZMod a) * c
    push_cast at hcast
    linear_combination -hcast
  have hvA := herzogLShapeCanonicality B e D _ _ hdA
  have hvIJ : physicalAlpha B e (A0 - (k * m : ZMod a)) =
      normalizedGrid B e 0 I J := by
    rw [hres]
    exact (herzogLShapeCanonicality B e D I J hdIJ).symm
  have hs := rawCandidate_spec B e k A0
  change (k : ℤ) * m + physicalAlpha B e (A0 - (k * m : ℕ)) -
      physicalAlpha B e A0 = (a : ℤ) * rawCandidate B e k A0 at hs
  have hvIJ' : physicalAlpha B e (A0 - (k * m : ℕ)) =
      normalizedGrid B e 0 I J := by simpa only [Nat.cast_mul] using hvIJ
  rw [hvIJ', ← hvA] at hs
  have hgIJ : normalizedGrid B e 0 I J = I * b + J * c := by
    simp only [normalizedGrid, zero_mul, zero_add]; rfl
  have hgA : normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) =
      (r31 R - 1) * b + (r32 R - 1) * c := by
    simp only [normalizedGrid, zero_mul, zero_add]; rfl
  rw [hgIJ, hgA] at hs
  push_cast at hbalance hs
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  have hvalue : rawCandidate B e k A0 = -S.coordinate.j := by
    nlinarith only [hs, hbalance, ha]
  have hnonpos : rawCandidate B e k A0 ≤ 0 := by rw [hvalue]; omega
  have hprefix := branchB_actualZeroEdgeBirth_axisC_high_seam_inner_notch_prefix_pos
    R hB x hsx hbirth haxis
  have hpositive := branchB_r2_prefix_candidate_positive R x hsx A0 hprefix hkpos hklt
  exact (not_lt_of_ge hnonpos) hpositive

private theorem branchB_r3_eta_row_antitone
    (R : SectorBCriticalRoleBranchB P) (i j t : ℕ)
    (hd : HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) (i + t) j) :
    eta P.M.base (branchBInactiveReindex R) (i + t) j ≤
      eta P.M.base (branchBInactiveReindex R) i j := by
  revert hd
  induction t with
  | zero => intro hd; simp
  | succ t ih =>
    intro hd
    have hp : HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) (i + t) j := by
      change _ < _ ∧ _ < _ ∧ (_ < _ ∨ _ < _) at hd ⊢
      omega
    have hs := eta_b_carry_transition P.M.base (branchBInactiveReindex R) (i + t) j
    rw [gridLift_eq_zero_on_herzogDomain _ _ _ hp,
      gridLift_eq_zero_on_herzogDomain _ _ _ (by simpa [Nat.add_assoc] using hd)] at hs
    have := ih hp
    change eta P.M.base (branchBInactiveReindex R) (i + t + 1) j ≤
      eta P.M.base (branchBInactiveReindex R) i j
    omega

private theorem branchB_r3_final_c_step
    (R : SectorBCriticalRoleBranchB P)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    physicalHeight P.M.base (branchBInactiveReindex R) r + branchBPrefixAmbientV R r =
      physicalHeight P.M.base (branchBInactiveReindex R) (r + routingC P.M.base (branchBInactiveReindex R)) +
        (routingData P.M.base (branchBInactiveReindex R)).v r := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hl0 := physicalHeight_spec B e r
  have hl1 := physicalHeight_spec B e (r + routingC B e)
  change (routingI B e).aperyRepresentative (routingA B e) r =
    physicalAlpha B e r + (routingA B e : ℤ) * physicalHeight B e r at hl0
  change (routingI B e).aperyRepresentative (routingA B e) (r + routingC B e) =
    physicalAlpha B e (r + routingC B e) +
      (routingA B e : ℤ) * physicalHeight B e (r + routingC B e) at hl1
  have hf := (routingI B e).apery_step_eq (routingA B e) (routingC B e) (routingHC B e) r
  have ha := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) r
  change physicalAlpha B e r + routingC B e = physicalAlpha B e (r + routingC B e) +
    (routingA B e : ℤ) * branchBPrefixAmbientV R r at ha
  change (routingI B e).aperyRepresentative (routingA B e) r + routingC B e =
    (routingI B e).aperyRepresentative (routingA B e) (r + routingC B e) +
      (routingA B e : ℤ) * (routingData B e).v r at hf
  have hpos : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have heq : (routingA B e : ℤ) *
      ((physicalHeight B e r : ℤ) + branchBPrefixAmbientV R r) =
    (routingA B e : ℤ) * (physicalHeight B e (r + routingC B e) + (routingData B e).v r) := by
    linear_combination hf - hl0 + hl1 - ha
  have := mul_left_cancel₀ (ne_of_gt hpos) heq
  exact_mod_cast this

/-- R3: the entire BN corridor has a strictly positive actual c-edge. -/
theorem branchB_high_axisC_bn_corridor_positive
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧ S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth = S.coordinate.j * normalizedC R)
    (t : ℕ) (ht : t < r21 R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let G := routingData B e
    0 < G.v (gridResidue B e (r31 R + t) (r32 R - 1)) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let N := gridResidue B e (r31 R + t) (r32 R - 1)
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have cp := L5A2C4D.coherent_coefficients_positive B e D
  have cs := L5A2C4D.coherent_coefficients B e D
  have hc := branchB_inactive_coherent_coefficients R
  have hq : 0 < r32 R := hc.2.1 ▸ cp.2.1
  have hdN : HerzogLShapeDomain D (r31 R + t) (r32 R - 1) := by
    change _ < _ ∧ _ < _ ∧ (_ < _ ∨ _ < _)
    rw [cs.2.1, cs.2.2, hc.1, hc.2.1, hc.2.2.2.2.2]
    omega
  have hdT : HerzogLShapeDomain D t 0 := by
    change _ < _ ∧ _ < _ ∧ (_ < _ ∨ _ < _)
    rw [cs.2.1, cs.2.2, hc.1, hc.2.1, hc.2.2.2.2.2]
    omega
  have hpacket := branchB_actualZeroEdgeBirth_axisC_high_seam_origin_inner_notch_final_packet
    R hB x hsx hbirth haxis
  have hzero : eta B e (r31 R + t) (r32 R - 1) = 0 := by
    have hh := branchB_r3_eta_row_antitone R (r31 R) (r32 R - 1) t hdN
    change eta B e (r31 R + t) (r32 R - 1) ≤ eta B e (r31 R) (r32 R - 1) at hh
    have hz := hpacket.2.1
    change eta B e (r31 R) (r32 R - 1) = 0 at hz
    omega
  have hbottom : eta B e t 0 ≤ S.coordinate.j.toNat := by
    have hh := branchB_r3_eta_row_antitone R 0 0 t (by simpa using hdT)
    have hz := hpacket.2.2.2
    simpa using hh.trans (le_of_eq hz)
  have hr := (L5A2C4OR5.coherent_normalized_relations B e D).1
  have hrel : c3 R * a = r31 R * b + r32 R * c := by
    change L5A2C4A.c1 B e * a = L5A2C4D.cr12 D * b + L5A2C4D.cr13 D * c at hr
    rw [hc.1, hc.2.1] at hr
    have hcrit := branchB_inactive_coherent_c1 R
    change L5A2C4A.c1 B e = c3 R at hcrit
    rwa [hcrit] at hr
  have hw : (r31 R + t) * b + (r32 R - 1) * c + c = t * b + c3 R * a := by
    rw [hrel]
    have hsub : r32 R - 1 + 1 = r32 R := by omega
    calc
      _ = t * b + (r31 R * b + (r32 R - 1 + 1) * c) := by ring
      _ = _ := by rw [hsub]
  have hwrap : N + (c : ZMod a) = gridResidue B e t 0 := by
    have hh := congrArg (fun n : ℕ => (n : ZMod a)) hw
    push_cast at hh
    simpa [N, gridResidue, normalizedGrid, a, b, c] using hh
  have hn := herzogLShapeCanonicality B e D _ _ hdN
  have htcan := herzogLShapeCanonicality B e D _ _ hdT
  have hamb := (routingH B e).asRelativeIdeal.apery_step_eq a c (routingHC B e) N
  change physicalAlpha B e N + c = physicalAlpha B e (N + (c : ZMod a)) +
    (a : ℤ) * branchBPrefixAmbientV R N at hamb
  rw [hwrap, ← hn, ← htcan] at hamb
  have hgN : normalizedGrid B e 0 (r31 R + t) (r32 R - 1) =
      (r31 R + t) * b + (r32 R - 1) * c := by
    simp only [normalizedGrid, zero_mul, zero_add]; rfl
  have hgT : normalizedGrid B e 0 t 0 = t * b := by
    simp only [normalizedGrid, zero_mul, zero_add, mul_zero, add_zero]; rfl
  rw [hgN, hgT] at hamb
  have hwi := congrArg (fun n : ℕ => (n : ℤ)) hw
  have hap : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  have hcarry : branchBPrefixAmbientV R N = c3 R := by
    simp only [Nat.cast_add, Nat.cast_mul] at hamb hwi
    have hp : (a : ℤ) * (branchBPrefixAmbientV R N : ℤ) = (a : ℤ) * c3 R := by
      rw [show c3 R = r13 R + r23 R from rfl]
      simp only [Nat.cast_add]
      linear_combination hwi - hamb
    have hi : (branchBPrefixAmbientV R N : ℤ) = c3 R := mul_left_cancel₀ (ne_of_gt hap) hp
    exact_mod_cast hi
  have hstep := branchB_r3_final_c_step R N
  rw [hwrap, hcarry, ← eta_eq_physicalHeight_on_herzogDomain B e D hdN,
    ← eta_eq_physicalHeight_on_herzogDomain B e D hdT, hzero] at hstep
  have hj : S.coordinate.j.toNat < c3 R := by
    have hu := haxis.2.2.1
    change S.coordinate.j < (qH R : ℤ) + vH R at hu
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    change c3 R = qH R + vH R at hsum
    have hl := haxis.2.1
    change (qH R : ℤ) < S.coordinate.j at hl
    have hnonneg : 0 ≤ S.coordinate.j := by omega
    omega
  change 0 < (routingData B e).v N
  change 0 + c3 R = eta B e t 0 + (routingData B e).v N at hstep
  omega

/-! B71 / Math-R4 only: numerical strict-bottom-drop engine. -/

private theorem branchB_r4_domain (R : SectorBCriticalRoleBranchB P) (i j : ℕ)
    (hi : i < c1 R) (hj : j < c2 R) (hc : i < r31 R ∨ j < r32 R) :
    HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) i j := by
  change _ < _ ∧ _ < _ ∧ (_ < _ ∨ _ < _)
  rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
    branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
  exact ⟨hi, hj, hc⟩

private theorem branchB_r4_alpha_grid (R : SectorBCriticalRoleBranchB P) (i j : ℕ)
    (hd : HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) i j) :
    physicalAlpha P.M.base (branchBInactiveReindex R)
      (gridResidue P.M.base (branchBInactiveReindex R) i j) =
    (i : ℤ) * routingB P.M.base (branchBInactiveReindex R) +
      (j : ℤ) * routingC P.M.base (branchBInactiveReindex R) := by
  have h := (herzogLShapeCanonicality _ _ _ i j hd).symm
  change physicalAlpha _ _ _ = (normalizedGrid _ _ 0 i j : ℤ) at h
  simp only [normalizedGrid, zero_mul, zero_add] at h
  simpa only [Nat.cast_add, Nat.cast_mul] using h

private theorem branchB_r4_candidate_edge
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (k g : ℕ)
    (hg : g ∈ routingH B e) (s : ZMod (routingA B e)) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    rawCandidate B e k (s + g) = rawCandidate B e k s +
      ((routingH B e).asRelativeIdeal.aperyStepQuotient (routingA B e) g hg s : ℤ) -
      (routingH B e).asRelativeIdeal.aperyStepQuotient (routingA B e) g hg
        (s - (k * routingM B e : ℕ)) := by
  let a := routingA B e
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have h0 := rawCandidate_spec B e k s
  have h1 := rawCandidate_spec B e k (s + g)
  change (k : ℤ) * routingM B e + physicalAlpha B e (s - (k * routingM B e : ℕ)) -
    physicalAlpha B e s = (a : ℤ) * rawCandidate B e k s at h0
  change (k : ℤ) * routingM B e + physicalAlpha B e (s + g - (k * routingM B e : ℕ)) -
    physicalAlpha B e (s + g) = (a : ℤ) * rawCandidate B e k (s + g) at h1
  have hb := (routingH B e).asRelativeIdeal.apery_step_eq a g hg s
  have ht := (routingH B e).asRelativeIdeal.apery_step_eq a g hg
    (s - (k * routingM B e : ℕ))
  change physicalAlpha B e s + g = physicalAlpha B e (s + g) +
    (a : ℤ) * _ at hb
  change physicalAlpha B e (s - (k * routingM B e : ℕ)) + g =
    physicalAlpha B e ((s - (k * routingM B e : ℕ)) + g) + (a : ℤ) * _ at ht
  have hres : s + (g : ZMod a) - (k * routingM B e : ℕ) =
      (s - (k * routingM B e : ℕ)) + g := by abel
  rw [hres] at h1
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  apply mul_left_cancel₀ (ne_of_gt ha)
  linear_combination h0 - h1 + hb - ht

private theorem branchB_r4_bt_geometry (R : SectorBCriticalRoleBranchB P)
    (i : ℕ) (hi : i < r31 R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let T := gridResidue B e i (c2 R - 1)
    let X := gridResidue B e (r21 R + i) 0
    HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) i (c2 R - 1) ∧
      HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) (r21 R + i) 0 ∧
      T + routingC B e = X ∧ branchBPrefixAmbientV R T = r23 R := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  have pos := (branchB_actual_herzog_coordinates R).cross_positive
  have sum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have sum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hz : 0 < r21 R := by simpa using pos.2.2.1
  have hq : 0 < r32 R := by simpa using pos.2.2.2.2.2
  have hdT := branchB_r4_domain R i (c2 R - 1) (by omega) (by omega) (Or.inl hi)
  have hdX := branchB_r4_domain R (r21 R + i) 0 (by omega) (by omega) (Or.inr hq)
  have hrel : c2 R * c = r23 R * a + r21 R * b := by
    change c2 R * routingC P.M.base (branchBInactiveReindex R) =
      r23 R * routingA P.M.base (branchBInactiveReindex R) +
        r21 R * routingB P.M.base (branchBInactiveReindex R)
    rw [branchB_inactive_routingA_eq_normalizedC, branchB_inactive_routingB_eq_normalizedA,
      branchB_inactive_routingC_eq_normalizedB]
    simpa only [uH, vH, add_comm] using
      (branchB_actual_herzog_coordinates R).normalized_relations.2.1
  have hw : i * b + (c2 R - 1) * c + c = (r21 R + i) * b + r23 R * a := by
    have hsub : c2 R - 1 + 1 = c2 R := by omega
    calc
      _ = i * b + (c2 R - 1 + 1) * c := by ring
      _ = _ := by rw [hsub, hrel]; ring
  have hr : gridResidue B e i (c2 R - 1) + c = gridResidue B e (r21 R + i) 0 := by
    have hh := congrArg (fun n : ℕ => (n : ZMod a)) hw
    push_cast at hh
    simpa [gridResidue, a, b, c] using hh
  refine ⟨hdT, hdX, hr, ?_⟩
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hs := (routingH B e).asRelativeIdeal.apery_step_eq a c (routingHC B e)
    (gridResidue B e i (c2 R - 1))
  change physicalAlpha B e (gridResidue B e i (c2 R - 1)) + c =
    physicalAlpha B e (gridResidue B e i (c2 R - 1) + c) +
      (a : ℤ) * branchBPrefixAmbientV R (gridResidue B e i (c2 R - 1)) at hs
  rw [hr, branchB_r4_alpha_grid R _ _ hdT, branchB_r4_alpha_grid R _ _ hdX] at hs
  have hwZ := congrArg (fun n : ℕ => (n : ℤ)) hw
  simp only [Nat.cast_add, Nat.cast_mul] at hwZ
  simp only [Nat.cast_add, Nat.cast_zero, zero_mul, add_zero] at hs
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  have heq : (a : ℤ) * branchBPrefixAmbientV R (gridResidue B e i (c2 R - 1)) =
      (a : ℤ) * r23 R := by linear_combination hwZ - hs
  exact_mod_cast (mul_left_cancel₀ (ne_of_gt ha) heq)

/-- R4-A: a zero final c-edge on BT determines the exact bottom height. -/
theorem branchB_bt_zero_height_identity (R : SectorBCriticalRoleBranchB P)
    (i : ℕ) (hi : i < r31 R)
    (hv : (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) = 0) :
    eta P.M.base (branchBInactiveReindex R) (r21 R + i) 0 =
      r23 R + eta P.M.base (branchBInactiveReindex R) i (c2 R - 1) := by
  obtain ⟨hdT, hdX, hr, hc⟩ := branchB_r4_bt_geometry R i hi
  have hs := branchB_r3_final_c_step R (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1))
  rw [hr, hc, ← eta_eq_physicalHeight_on_herzogDomain _ _ _ hdT,
    ← eta_eq_physicalHeight_on_herzogDomain _ _ _ hdX, hv] at hs
  omega

/-- R4-B includes zero height: no raw-minimum-zero premise is used. -/
theorem branchB_bt_zero_rawMinimum_eq_eta (R : SectorBCriticalRoleBranchB P)
    (i : ℕ) (hi : i < r31 R)
    (hv : (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) = 0) :
    rawMinimum P.M.base (branchBInactiveReindex R)
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) =
      eta P.M.base (branchBInactiveReindex R) i (c2 R - 1) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let T := gridResidue B e i (c2 R - 1)
  let X := gridResidue B e (r21 R + i) 0
  obtain ⟨hdT, hdX, hr, hc⟩ := branchB_r4_bt_geometry R i hi
  have hh := branchB_bt_zero_height_identity R i hi hv
  have hw : 0 < r23 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.1
  have hx := physicalHeight_eq_max_rawMinimum B e X
  rw [← eta_eq_physicalHeight_on_herzogDomain B e _ hdX] at hx
  change (eta B e (r21 R + i) 0 : ℤ) = max 0 (rawMinimum B e X) at hx
  change eta B e (r21 R + i) 0 = r23 R + eta B e i (c2 R - 1) at hh
  have hminX : rawMinimum B e X = eta B e (r21 R + i) 0 := by omega
  have ht := physicalHeight_eq_max_rawMinimum B e T
  rw [← eta_eq_physicalHeight_on_herzogDomain B e _ hdT] at ht
  let k := currentSelector B e T
  have hk := currentSelector_pos B e T
  have hval := rawCandidate_currentSelector B e T
  have he := branchB_r4_candidate_edge B e k (routingC B e) (routingHC B e) T
  change rawCandidate B e k (T + routingC B e) = rawCandidate B e k T +
    (branchBPrefixAmbientV R T : ℤ) - branchBPrefixAmbientV R (T - (k * routingM B e : ℕ)) at he
  rw [hr, hc] at he
  change rawCandidate B e k X = rawCandidate B e k T + (r23 R : ℤ) -
    branchBPrefixAmbientV R (T - (k * routingM B e : ℕ)) at he
  have hl := rawMinimum_le B e X hk
  change rawMinimum B e X ≤ rawCandidate B e k X at hl
  change rawCandidate B e k T = rawMinimum B e T at hval
  change rawMinimum B e T = eta B e i (c2 R - 1)
  omega

private theorem branchB_r4_bottom_geometry (R : SectorBCriticalRoleBranchB P)
    (i : ℕ) (hi : i < r31 R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let L := gridResidue B e (r21 R + i - 1) 0
    let X := gridResidue B e (r21 R + i) 0
    HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) (r21 R + i - 1) 0 ∧
      L + routingB B e = X ∧ branchBPrefixAmbientU R L = 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let b := routingB B e
  have hz : 0 < r21 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
  have hq : 0 < r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hsum : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hd := branchB_r4_domain R (r21 R + i - 1) 0 (by omega) (by omega) (Or.inr hq)
  have hdX := (branchB_r4_bt_geometry R i hi).2.1
  have hsucc : r21 R + i - 1 + 1 = r21 R + i := by omega
  have hr : gridResidue B e (r21 R + i - 1) 0 + b = gridResidue B e (r21 R + i) 0 := by
    rw [← gridResidue_add_b, hsucc]
  refine ⟨hd, hr, ?_⟩
  have hs := branchB_inactive_b_carry_spec R (gridResidue B e (r21 R + i - 1) 0)
  change physicalAlpha B e (gridResidue B e (r21 R + i - 1) 0) + b =
    physicalAlpha B e (gridResidue B e (r21 R + i - 1) 0 + b) +
      (a : ℤ) * branchBPrefixAmbientU R (gridResidue B e (r21 R + i - 1) 0) at hs
  rw [hr, branchB_r4_alpha_grid R _ _ hd, branchB_r4_alpha_grid R _ _ hdX] at hs
  simp only [Nat.cast_zero, zero_mul, add_zero] at hs
  have hsucci := congrArg (fun n : ℕ => (n : ℤ)) hsucc
  simp only [Nat.cast_add, Nat.cast_one] at hsucci
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  have hp : (a : ℤ) * branchBPrefixAmbientU R (gridResidue B e (r21 R + i - 1) 0) = 0 := by
    change ((r21 R + i - 1 : ℕ) : ℤ) * b + b =
      ((r21 R + i : ℕ) : ℤ) * b + (a : ℤ) * _ at hs
    simp only [Nat.cast_add] at hs
    rw [← hsucci] at hs
    linear_combination -hs
  have hz := (mul_eq_zero.mp hp).resolve_left (ne_of_gt ha)
  exact_mod_cast hz

/-- Transport an arbitrary genuine BT minimizer; no ownership is preserved. -/
theorem branchB_bt_minimizer_translated_carry_zero
    (R : SectorBCriticalRoleBranchB P) (i : ℕ) (hi : i < r31 R)
    (hv : (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) = 0)
    (k : ℕ) (hk : 0 < k)
    (hmin : rawCandidate P.M.base (branchBInactiveReindex R) k
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) =
      eta P.M.base (branchBInactiveReindex R) i (c2 R - 1)) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let T := gridResidue B e i (c2 R - 1)
    let X := gridResidue B e (r21 R + i) 0
    branchBPrefixAmbientV R (T - (k * routingM B e : ℕ)) = 0 ∧
      rawCandidate B e k X = eta B e (r21 R + i) 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let T := gridResidue B e i (c2 R - 1)
  let X := gridResidue B e (r21 R + i) 0
  obtain ⟨hdT, hdX, hr, hc⟩ := branchB_r4_bt_geometry R i hi
  have hh := branchB_bt_zero_height_identity R i hi hv
  change eta B e (r21 R + i) 0 = r23 R + eta B e i (c2 R - 1) at hh
  have hw : 0 < r23 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.1
  have hx := physicalHeight_eq_max_rawMinimum B e X
  rw [← eta_eq_physicalHeight_on_herzogDomain B e _ hdX] at hx
  change (eta B e (r21 R + i) 0 : ℤ) = max 0 (rawMinimum B e X) at hx
  have hmx : rawMinimum B e X = eta B e (r21 R + i) 0 := by omega
  have he := branchB_r4_candidate_edge B e k (routingC B e) (routingHC B e) T
  change rawCandidate B e k (T + routingC B e) = rawCandidate B e k T +
    (branchBPrefixAmbientV R T : ℤ) - branchBPrefixAmbientV R (T - (k * routingM B e : ℕ)) at he
  rw [hr, hc] at he
  change rawCandidate B e k X = rawCandidate B e k T + (r23 R : ℤ) -
    branchBPrefixAmbientV R (T - (k * routingM B e : ℕ)) at he
  change rawCandidate B e k T = eta B e i (c2 R - 1) at hmin
  have hl := rawMinimum_le B e X hk
  rw [hmx] at hl
  change branchBPrefixAmbientV R (T - (k * routingM B e : ℕ)) = 0 ∧
    rawCandidate B e k X = eta B e (r21 R + i) 0
  constructor <;> omega

private theorem branchB_r4_alpha_nonneg (R : SectorBCriticalRoleBranchB P)
    (s : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    0 ≤ physicalAlpha P.M.base (branchBInactiveReindex R) s := by
  obtain ⟨I, J, hd, hr, hv⟩ := branchB_physicalAlpha_canonical_coordinates R s
  rw [hv]
  exact Nat.cast_nonneg _

private theorem branchB_r4_tail_hit_mem
    (R : SectorBCriticalRoleBranchB P) (i : ℕ) (hi : i < r31 R) (k : ℕ)
    (hmin : rawCandidate P.M.base (branchBInactiveReindex R) k
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) =
        eta P.M.base (branchBInactiveReindex R) i (c2 R - 1))
    (hcv : branchBPrefixAmbientV R
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1) -
        (k * routingM P.M.base (branchBInactiveReindex R) : ℕ)) = 0)
    (hbu : 0 < branchBPrefixAmbientU R
      (gridResidue P.M.base (branchBInactiveReindex R) (r21 R + i - 1) 0 -
        (k * routingM P.M.base (branchBInactiveReindex R) : ℕ))) :
    k * routingM P.M.base (branchBInactiveReindex R) ∈
      routingH P.M.base (branchBInactiveReindex R) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let m := routingM B e
  let T := gridResidue B e i (c2 R - 1)
  let L := gridResidue B e (r21 R + i - 1) 0
  let V := T - (k * m : ℕ)
  let U := L - (k * m : ℕ)
  let h := eta B e i (c2 R - 1)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  obtain ⟨hdT, hdX, hTc, _⟩ := branchB_r4_bt_geometry R i hi
  obtain ⟨_, hLb, _⟩ := branchB_r4_bottom_geometry R i hi
  have hjoin : U + b = V + c := by
    change L - (k * m : ℕ) + b = T - (k * m : ℕ) + c
    calc
      _ = (L + b) - (k * m : ℕ) := by abel
      _ = (T + c) - (k * m : ℕ) := by rw [hLb, hTc]
      _ = _ := by abel
  have hs := rawCandidate_spec B e k T
  change (k : ℤ) * m + physicalAlpha B e V - physicalAlpha B e T =
    (a : ℤ) * rawCandidate B e k T at hs
  change rawCandidate B e k T = h at hmin
  rw [hmin, branchB_r4_alpha_grid R _ _ hdT] at hs
  change (k : ℤ) * m + physicalAlpha B e V -
    ((i : ℤ) * b + ((c2 R - 1 : ℕ) : ℤ) * c) = (a : ℤ) * h at hs
  have hvstep := (routingH B e).asRelativeIdeal.apery_step_eq a c (routingHC B e) V
  change physicalAlpha B e V + c = physicalAlpha B e (V + c) +
    (a : ℤ) * branchBPrefixAmbientV R V at hvstep
  change branchBPrefixAmbientV R V = 0 at hcv
  rw [hcv, Nat.cast_zero, mul_zero, add_zero, ← hjoin] at hvstep
  have tri := branchB_inactive_b_carry_trichotomy R U
  change branchBPrefixAmbientU R U = 0 ∨
    (∃ t, U = gridResidue B e (c1 R - 1) t ∧ t < r32 R ∧
      branchBPrefixAmbientU R U = r13 R ∧ U + b = gridResidue B e 0 (r12 R + t)) ∨
    (∃ t, U = gridResidue B e (r31 R - 1) t ∧ r32 R ≤ t ∧ t < c2 R ∧
      branchBPrefixAmbientU R U = c3 R ∧ U + b = gridResidue B e 0 (t - r32 R)) at tri
  change 0 < branchBPrefixAmbientU R U at hbu
  have hq : 0 < r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hp : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hc2pos : 1 ≤ c2 R := by omega
  rcases tri with hz | ⟨t, hu, ht, _, hnext⟩ | ⟨t, hu, htq, ht, _, hnext⟩
  · omega
  · have hd := branchB_r4_domain R 0 (r12 R + t) (by omega) (by omega) (Or.inl hp)
    rw [hnext, branchB_r4_alpha_grid R _ _ hd] at hvstep
    simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add] at hvstep
    let n := h * a + i * b + (r32 R - t) * c
    have hn : n ∈ routingH B e := by
      change n ∈ generatedThree a b c
      exact (mem_generatedThree_iff _ _ _ _).2 ⟨h, i, r32 R - t, rfl⟩
    have heq : (k * m : ℕ) = n := by
      have heqi : ((k * m : ℕ) : ℤ) = n := by
        dsimp only [n]
        simp only [Nat.cast_add, Nat.cast_mul]
        rw [Nat.cast_sub (by omega : t ≤ r32 R)]
        rw [Nat.cast_sub hc2pos] at hs
        have hsumZ := congrArg (fun n : ℕ => (n : ℤ)) hsum2
        simp only [Nat.cast_add] at hsumZ
        rw [hsumZ] at hs
        linear_combination hs - hvstep
      exact_mod_cast heqi
    change k * m ∈ routingH B e
    rwa [heq]
  · have hd := branchB_r4_domain R 0 (t - r32 R) (by omega) (by omega) (Or.inl hp)
    rw [hnext, branchB_r4_alpha_grid R _ _ hd] at hvstep
    simp only [Nat.cast_zero, zero_mul, zero_add] at hvstep
    have hstrict : r32 R < t := by
      by_contra hn
      have heq : t = r32 R := by omega
      rw [heq, Nat.sub_self, Nat.cast_zero, zero_mul] at hvstep
      have hvnonneg := branchB_r4_alpha_nonneg R V
      change 0 ≤ physicalAlpha B e V at hvnonneg
      have hcpos : (0 : ℤ) < c := by
        have hnat : 0 < c := by
          change 0 < routingC P.M.base (branchBInactiveReindex R)
          rw [branchB_inactive_routingC_eq_normalizedB]
          have hscale := L5A2B4AR3.normalizedWeight_scale P.M.base (R.reindex 1)
          have hweight := L2B.weights_positive P.M.base (R.reindex 1)
          change 0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex 1)
          nlinarith
        exact_mod_cast hnat
      omega
    let n := h * a + i * b + (c2 R + r32 R - t) * c
    have hn : n ∈ routingH B e := by
      change n ∈ generatedThree a b c
      exact (mem_generatedThree_iff _ _ _ _).2 ⟨h, i, c2 R + r32 R - t, rfl⟩
    have heq : (k * m : ℕ) = n := by
      have heqi : ((k * m : ℕ) : ℤ) = n := by
        dsimp only [n]
        simp only [Nat.cast_add, Nat.cast_mul]
        rw [Nat.cast_sub (by omega : t ≤ c2 R + r32 R)]
        simp only [Nat.cast_add] 
        rw [Nat.cast_sub hc2pos] at hs
        rw [Nat.cast_sub htq] at hvstep
        linear_combination hs - hvstep
      exact_mod_cast heqi
    change k * m ∈ routingH B e
    rwa [heq]

/-- R4 numerical form of the preceding exceptional transverse strictness.
The drop is on the same bottom b-edge, including i=0. No minimizer
uniqueness, selector equality or owner persistence is asserted. -/
theorem branchB_high_axisC_bt_zero_principal_minimizer
    (R : SectorBCriticalRoleBranchB P) (i : ℕ) (hi : i < r31 R)
    (hv : (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) = 0)
    (hdrop : eta P.M.base (branchBInactiveReindex R) (r21 R + i) 0 <
      eta P.M.base (branchBInactiveReindex R) (r21 R + i - 1) 0) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let T := gridResidue B e i (c2 R - 1)
    rawMinimum B e T = eta B e i (c2 R - 1) ∧
      rawCandidate B e (actualPrincipalIndex B) T = rawMinimum B e T := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let T := gridResidue B e i (c2 R - 1)
  let X := gridResidue B e (r21 R + i) 0
  let L := gridResidue B e (r21 R + i - 1) 0
  let m := routingM B e
  change eta B e (r21 R + i) 0 < eta B e (r21 R + i - 1) 0 at hdrop
  have hmin := branchB_bt_zero_rawMinimum_eq_eta R i hi hv
  change rawMinimum B e T = eta B e i (c2 R - 1) at hmin
  let q := currentSelector B e T
  have hq := currentSelector_pos B e T
  obtain ⟨k, hk, hkle, hreduce⟩ := branchB_candidate_reduce_to_first_principal_block R T hq
  have hl := rawMinimum_le B e T hk
  have hqval := rawCandidate_currentSelector B e T
  have hkmin : rawCandidate B e k T = eta B e i (c2 R - 1) := by
    rw [hmin] at hl
    change rawCandidate B e q T = rawMinimum B e T at hqval
    rw [hqval, hmin] at hreduce
    exact le_antisymm hreduce hl
  obtain ⟨hcv, hkX⟩ := branchB_bt_minimizer_translated_carry_zero R i hi hv k hk hkmin
  obtain ⟨hdL, hr, hc⟩ := branchB_r4_bottom_geometry R i hi
  have hh := physicalHeight_eq_max_rawMinimum B e L
  rw [← eta_eq_physicalHeight_on_herzogDomain B e _ hdL] at hh
  change (eta B e (r21 R + i - 1) 0 : ℤ) = max 0 (rawMinimum B e L) at hh
  have hmx : rawMinimum B e L = eta B e (r21 R + i - 1) 0 := by omega
  have he := branchB_r4_candidate_edge B e k (routingB B e) (routingHB B e) L
  change rawCandidate B e k (L + routingB B e) = rawCandidate B e k L +
    (branchBPrefixAmbientU R L : ℤ) - branchBPrefixAmbientU R (L - (k * m : ℕ)) at he
  rw [hr, hc] at he
  change rawCandidate B e k X = rawCandidate B e k L + (0 : ℤ) -
    branchBPrefixAmbientU R (L - (k * m : ℕ)) at he
  have hlL := rawMinimum_le B e L hk
  rw [hmx] at hlL
  change (eta B e (r21 R + i - 1) 0 : ℤ) ≤ rawCandidate B e k L at hlL
  change rawCandidate B e k X = eta B e (r21 R + i) 0 at hkX
  have hbu : 0 < branchBPrefixAmbientU R (L - (k * m : ℕ)) := by omega
  have hmem := branchB_r4_tail_hit_mem R i hi k hkmin hcv hbu
  have hmemN : k * normalizedM B ∈ normalizedH B := by
    rw [← branchBRoutingH_eq_normalizedH R]
    simpa [routingM, normalizedM] using hmem
  have hQle := principalIndex_min (normalizedH B) (normalizedM B) B.q_positive hk hmemN
  have hkQ : k = actualPrincipalIndex B := le_antisymm hkle hQle
  change rawMinimum B e T = eta B e i (c2 R - 1) ∧
    rawCandidate B e (actualPrincipalIndex B) T = rawMinimum B e T
  exact ⟨hmin, by rw [← hkQ, hkmin, hmin]⟩

/-! B72 / Math-R5: same-root first BT zero and the two location bounds. -/

private theorem branchB_r5_b_pow_grid (R : SectorBCriticalRoleBranchB P)
    (i j n : ℕ) :
    ((routingData P.M.base (branchBInactiveReindex R)).b ^ n)
      (gridResidue P.M.base (branchBInactiveReindex R) i j) =
        gridResidue P.M.base (branchBInactiveReindex R) (i + n) j := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (routingData B e).b
      (((routingData B e).b ^ n) (gridResidue B e i j)) = _
    rw [ih]
    change gridResidue B e (i + n) j + routingB B e = _
    rw [← gridResidue_add_b]
    congr 1 <;> omega

private theorem branchB_r5_bn_bt_wrap (R : SectorBCriticalRoleBranchB P) (i : ℕ) :
    gridResidue P.M.base (branchBInactiveReindex R) (c1 R + i) (r32 R - 1) =
      gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  have hq : 0 < r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hsum : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hrel : c1 R * b = r13 R * a + r12 R * c := by
    change c1 R * routingB P.M.base (branchBInactiveReindex R) =
      r13 R * routingA P.M.base (branchBInactiveReindex R) +
      r12 R * routingC P.M.base (branchBInactiveReindex R)
    rw [branchB_inactive_routingA_eq_normalizedC,
      branchB_inactive_routingB_eq_normalizedA,
      branchB_inactive_routingC_eq_normalizedB]
    simpa only [qH, add_comm] using
      (branchB_actual_herzog_coordinates R).normalized_relations.1
  have heq : (c1 R + i) * b + (r32 R - 1) * c =
      i * b + (c2 R - 1) * c + r13 R * a := by
    have hc : r12 R + (r32 R - 1) = c2 R - 1 := by omega
    rw [add_mul, hrel]
    rw [← hc]
    ring
  have hcast := congrArg (fun n : ℕ => (n : ZMod a)) heq
  push_cast at hcast
  rw [show (a : ZMod a) = 0 from ZMod.natCast_self a, mul_zero, add_zero] at hcast
  change ((c1 R + i : ℕ) : ZMod a) * b + ((r32 R - 1 : ℕ) : ZMod a) * c =
    (i : ZMod a) * b + ((c2 R - 1 : ℕ) : ZMod a) * c
  simpa only [Nat.cast_add] using hcast

private theorem branchB_r5_final_b_step (R : SectorBCriticalRoleBranchB P)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    physicalHeight P.M.base (branchBInactiveReindex R) r + branchBPrefixAmbientU R r =
      physicalHeight P.M.base (branchBInactiveReindex R)
        (r + routingB P.M.base (branchBInactiveReindex R)) +
      (routingData P.M.base (branchBInactiveReindex R)).u r := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let b := routingB B e
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have h0 := physicalHeight_spec B e r
  have h1 := physicalHeight_spec B e (r + b)
  have hf := (routingI B e).apery_step_eq a b (routingHB B e) r
  have ha := branchB_inactive_b_carry_spec R r
  change (routingI B e).aperyRepresentative a r =
    physicalAlpha B e r + (a : ℤ) * physicalHeight B e r at h0
  change (routingI B e).aperyRepresentative a (r + b) =
    physicalAlpha B e (r + b) + (a : ℤ) * physicalHeight B e (r + b) at h1
  change (routingI B e).aperyRepresentative a r + b =
    (routingI B e).aperyRepresentative a (r + b) +
      (a : ℤ) * (routingData B e).u r at hf
  change physicalAlpha B e r + b = physicalAlpha B e (r + b) +
    (a : ℤ) * branchBPrefixAmbientU R r at ha
  have hap : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  have hm : (a : ℤ) * ((physicalHeight B e r : ℤ) + branchBPrefixAmbientU R r) =
      (a : ℤ) * (physicalHeight B e (r + b) + (routingData B e).u r) := by
    linear_combination hf - h0 + h1 - ha
  exact_mod_cast (mul_left_cancel₀ (ne_of_gt hap) hm)

private theorem branchB_r5_principal_bt_candidate
    (R : SectorBCriticalRoleBranchB P) (P0 T0 : ℕ)
    (hcoord : actualPrincipalIndex P.M.base *
      routingM P.M.base (branchBInactiveReindex R) =
      P0 * routingB P.M.base (branchBInactiveReindex R) +
      T0 * routingC P.M.base (branchBInactiveReindex R))
    (hP : P0 < r31 R) (hT : T0 < r32 R) (i : ℕ) (hi : i < r31 R) :
    rawCandidate P.M.base (branchBInactiveReindex R) (actualPrincipalIndex P.M.base)
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) =
        if i < P0 then (r13 R : ℤ) else 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let Q := actualPrincipalIndex B
  let m := routingM B e
  let T := gridResidue B e i (c2 R - 1)
  have pos := (branchB_actual_herzog_coordinates R).cross_positive
  have hp : 0 < r31 R := by simpa using pos.2.2.2.2.1
  have hq : 0 < r32 R := by simpa using pos.2.2.2.2.2
  have hz : 0 < r21 R := by simpa using pos.2.2.1
  have sum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have sum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hdT := (branchB_r4_bt_geometry R i hi).1
  have finish (I J w : ℕ)
      (hd : HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) I J)
      (hb : Q * m + I * b + J * c = i * b + (c2 R - 1) * c + w * a) :
      rawCandidate B e Q T = w := by
    have hcast := congrArg (fun n : ℕ => (n : ZMod a)) hb
    push_cast at hcast
    rw [show (a : ZMod a) = 0 from ZMod.natCast_self a, mul_zero, add_zero] at hcast
    have hr : T - (Q * m : ℕ) = gridResidue B e I J := by
      change (i : ZMod a) * b + ((c2 R - 1 : ℕ) : ZMod a) * c -
        ((Q * m : ℕ) : ZMod a) = (I : ZMod a) * b + (J : ZMod a) * c
      push_cast
      linear_combination -hcast
    have hs := rawCandidate_spec B e Q T
    change (Q : ℤ) * m + physicalAlpha B e (T - (Q * m : ℕ)) -
      physicalAlpha B e T = (a : ℤ) * rawCandidate B e Q T at hs
    rw [hr, branchB_r4_alpha_grid R _ _ hd, branchB_r4_alpha_grid R _ _ hdT] at hs
    have hbi := congrArg (fun n : ℕ => (n : ℤ)) hb
    push_cast at hbi
    have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
    nlinarith only [hs, hbi, ha]
  change rawCandidate B e Q T = if i < P0 then (r13 R : ℤ) else 0
  by_cases hlt : i < P0
  · rw [if_pos hlt]
    let I := c1 R + i - P0
    let J := c2 R - 1 - T0 - r12 R
    have hI : I + P0 = c1 R + i := by dsimp [I]; omega
    have hJ : J + T0 + r12 R = c2 R - 1 := by dsimp [J]; omega
    have hd := branchB_r4_domain R I J (by dsimp [I]; omega)
      (by dsimp [J]; omega) (Or.inr (by dsimp [J]; omega))
    apply finish I J (r13 R) hd
    have hrel : c1 R * b = r13 R * a + r12 R * c := by
      change c1 R * routingB P.M.base (branchBInactiveReindex R) =
        r13 R * routingA P.M.base (branchBInactiveReindex R) +
        r12 R * routingC P.M.base (branchBInactiveReindex R)
      rw [branchB_inactive_routingA_eq_normalizedC,
        branchB_inactive_routingB_eq_normalizedA,
        branchB_inactive_routingC_eq_normalizedB]
      simpa only [qH, add_comm] using (branchB_actual_herzog_coordinates R).normalized_relations.1
    change Q * m = P0 * b + T0 * c at hcoord
    rw [hcoord]
    nlinarith only [hrel, congrArg (fun n => n * b) hI, congrArg (fun n => n * c) hJ]
  · rw [if_neg hlt]
    let I := i - P0
    let J := c2 R - 1 - T0
    have hI : I + P0 = i := by dsimp [I]; omega
    have hJ : J + T0 = c2 R - 1 := by dsimp [J]; omega
    have hd := branchB_r4_domain R I J (by dsimp [I]; omega)
      (by dsimp [J]; omega) (Or.inl (by dsimp [I]; omega))
    have hh := finish I J 0 hd (by
      change Q * m = P0 * b + T0 * c at hcoord
      rw [hcoord]
      nlinarith only [congrArg (fun n => n * b) hI, congrArg (fun n => n * c) hJ])
    simpa using hh

section B72Packet
variable (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
  (x : BranchBActualExceptionalBranches P R)
  (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
    (actualPrincipalIndex P.M.base) (branchBActualExceptionalNormalizedSource P R x).val)
  (hbirth : IsActualZeroEdgeBirth R x hsx)
  (haxis :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
    S.coordinate.j < qH R + vH R ∧ S.beta = S.coordinate.j * normalizedC R ∧
    (S.n : ℤ) + normalizedA R * S.depth = S.coordinate.j * normalizedC R)

include hB x hsx hbirth haxis in
/-- A hypothetical first BT zero identifies its own preceding canonical
B endpoint, not kappa2, and gives the exact R4 bottom drop. -/
theorem branchB_high_axisC_first_bt_zero_strict_drop
    (i : ℕ) (hi : i < r31 R)
    (hz : (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) = 0)
    (hfirst : ∀ t < i, 0 < (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R) t (c2 R - 1))) :
    eta P.M.base (branchBInactiveReindex R) (r21 R + i) 0 <
      eta P.M.base (branchBInactiveReindex R) (r21 R + i - 1) 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let G := routingData B e
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let A := gridResidue B e (r31 R - 1) (r32 R - 1)
  let n := r21 R + 1 + i
  let n0 := L5A2C4I.ResidueData.bFirstZeroIndex G x.val.val
  have hp : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hq : 0 < r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hzpos : 0 < r21 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
  have hsum : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hbase : x.val.val.val = A :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_base_eq_inner_notch
      R hB x hsx hbirth haxis
  have hBN (t : ℕ) : (G.b ^ (t + 1)) A =
      gridResidue B e (r31 R + t) (r32 R - 1) := by
    rw [branchB_r5_b_pow_grid]
    congr 1 <;> omega
  have hBT (t : ℕ) : (G.b ^ (r21 R + 1 + t)) A =
      gridResidue B e t (c2 R - 1) := by
    rw [branchB_r5_b_pow_grid]
    have hcoord : r31 R - 1 + (r21 R + 1 + t) = c1 R + t := by omega
    rw [hcoord, branchB_r5_bn_bt_wrap]
  have hpositive : ∀ k, 0 < k → k < n → 0 < G.v ((G.b ^ k) A) := by
    intro k hk hkn
    by_cases hBNk : k ≤ r21 R
    · have heq : k = (k - 1) + 1 := by omega
      rw [heq, hBN]
      exact branchB_high_axisC_bn_corridor_positive R hB x hsx hbirth haxis
        (k - 1) (by omega)
    · have heq : k = r21 R + 1 + (k - (r21 R + 1)) := by omega
      rw [heq, hBT]
      exact hfirst (k - (r21 R + 1)) (by dsimp [n] at hkn; omega)
  have hzero : G.v ((G.b ^ n) A) = 0 := by
    rw [hBT]; exact hz
  have hnpos : 0 < n := by dsimp [n]; omega
  have hn0pos := L5A2C4I.ResidueData.firstZeroIndex_pos G.b G.v
    x.val.val.val x.val.val.property.1.2
  have hn0zero := L5A2C4I.ResidueData.firstZeroIndex_zero G.b G.v
    x.val.val.val x.val.val.property.1.2
  change 0 < n0 at hn0pos
  change G.v ((G.b ^ n0) x.val.val.val) = 0 at hn0zero
  have hn0 : n0 = n := by
    apply le_antisymm
    · by_contra h
      have hl : n < n0 := by omega
      have hpos := L5A2C4I.ResidueData.firstZeroIndex_positive_before G.b G.v
        x.val.val.val x.val.val.property.1.2 hnpos hl
      rw [hbase] at hpos
      exact (Nat.ne_of_gt hpos) hzero
    · by_contra h
      have hl : n0 < n := by omega
      have hpos := hpositive n0 hn0pos hl
      rw [hbase] at hn0zero
      exact (Nat.ne_of_gt hpos) hn0zero
  let E := L5A2C4I.ResidueData.canonicalBEndpoint G x.val.val
  let L := gridResidue B e (r21 R + i - 1) 0
  have hE : E = gridResidue B e (r31 R - 1 + (n - 1)) (r32 R - 1) := by
    change (G.b ^ (n0 - 1)) x.val.val.val = _
    rw [hn0, hbase, branchB_r5_b_pow_grid]
  have hrel : c3 R * a = r31 R * b + r32 R * c := by
    change c3 R * routingA P.M.base (branchBInactiveReindex R) =
      r31 R * routingB P.M.base (branchBInactiveReindex R) +
      r32 R * routingC P.M.base (branchBInactiveReindex R)
    rw [branchB_inactive_routingA_eq_normalizedC,
      branchB_inactive_routingB_eq_normalizedA,
      branchB_inactive_routingC_eq_normalizedB]
    simpa using (branchB_actual_herzog_coordinates R).normalized_relations.2.2
  have hCE : G.c E = L := by
    change E + c = L
    rw [hE]
    have hcoord : r31 R - 1 + (n - 1) = r31 R + (r21 R + i - 1) := by
      dsimp [n]; omega
    have hqc : r32 R - 1 + 1 = r32 R := by omega
    have heq : (r31 R + (r21 R + i - 1)) * b + (r32 R - 1) * c + c =
        (r21 R + i - 1) * b + c3 R * a := by
      rw [hrel]
      nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ r32 R)]
    have hcast := congrArg (fun t : ℕ => (t : ZMod a)) heq
    push_cast at hcast
    rw [show (a : ZMod a) = 0 from ZMod.natCast_self a, mul_zero, add_zero] at hcast
    rw [hcoord]
    dsimp only [L, gridResidue]
    simp only [Nat.cast_add, Nat.cast_zero, zero_mul, add_zero]
    exact hcast
  have hex := (branchB_actualExceptional_endpoint_kernel P R x).2.2.2.2
  change 0 < G.u (G.c E) at hex
  rw [hCE] at hex
  obtain ⟨hdL, hLb, hcL⟩ := branchB_r4_bottom_geometry R i hi
  have hdX := (branchB_r4_bt_geometry R i hi).2.1
  have hstep := branchB_r5_final_b_step R L
  rw [hLb, hcL, ← eta_eq_physicalHeight_on_herzogDomain _ _ _ hdL,
    ← eta_eq_physicalHeight_on_herzogDomain _ _ _ hdX] at hstep
  change eta B e (r21 R + i - 1) 0 + 0 =
    eta B e (r21 R + i) 0 + G.u L at hstep
  change eta B e (r21 R + i) 0 < eta B e (r21 R + i - 1) 0
  omega

include hB x hsx hbirth haxis in
private theorem branchB_r5_selected_candidate_le_individual
    (i t : ℕ)
    (hd : HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) i t) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    rawCandidate P.M.base (branchBInactiveReindex R) S.ell
      (gridResidue P.M.base (branchBInactiveReindex R) i t) ≤
      branchBHighSeamIndividualHeight R S.coordinate.j.toNat S.depth i t := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let H := routingH B e
  let a := routingA B e
  let r := gridResidue B e i t
  let height := branchBHighSeamIndividualHeight R S.coordinate.j.toNat S.depth i t
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hf := branchB_high_seam_individual_height_formula R hB x hsx hbirth haxis i t hd
  change (returnIdeal H S.n).aperyRepresentative a r =
    physicalAlpha B e r + a * height at hf
  have hm := (returnIdeal H S.n).aperyRepresentative_mem a r
  rw [hf, mem_returnIdeal_iff] at hm
  have hn : S.n = S.ell * routingM B e := by simpa [routingM] using S.n_eq
  have hsub := hm.2
  rw [hn] at hsub
  exact (rawCandidate_threshold B e r S.ell_pos height).1 hsub

include hB x hsx hbirth haxis in
/-- Any BT zero lies strictly before the selected-return bottom threshold.
The B59 representative is connected to a genuine raw candidate by its
return-ideal membership and the exact candidate threshold theorem. -/
theorem branchB_high_axisC_bt_zero_selected_location
    (i : ℕ) (hi : i < r31 R)
    (hz : (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) = 0) :
    i < r31 R - (branchB_actual_selected_return_anchor_v2 R hB hsx).depth := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let j := S.coordinate.j.toNat
  let X := gridResidue B e (r21 R + i) 0
  have hq : 0 < r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum3 : c3 R = r13 R + r23 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
  have hj : r13 R < j ∧ j < c3 R := by
    have hl := haxis.2.1
    have hu := haxis.2.2.1
    change (r13 R : ℤ) < S.coordinate.j at hl
    change S.coordinate.j < (r13 R : ℤ) + r23 R at hu
    dsimp only [j]
    omega
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31 R hB x hsx hbirth haxis
  change i < r31 R - S.depth
  by_contra hnot
  have hthreshold : c1 R - S.depth ≤ r21 R + i := by omega
  obtain ⟨_, hdX, _, _⟩ := branchB_r4_bt_geometry R i hi
  have hcand := branchB_r5_selected_candidate_le_individual R hB x hsx hbirth haxis
    (r21 R + i) 0 hdX
  have heval : branchBHighSeamIndividualHeight R j S.depth (r21 R + i) 0 =
      j - r13 R := by
    simp only [branchBHighSeamIndividualHeight, hq, if_pos,
      if_neg (by omega : ¬ r21 R + i < c1 R - S.depth)]
  change rawCandidate B e S.ell X ≤
    branchBHighSeamIndividualHeight R j S.depth (r21 R + i) 0 at hcand
  rw [heval] at hcand
  have hmin := rawMinimum_le B e X S.ell_pos
  have hheight := physicalHeight_eq_max_rawMinimum B e X
  rw [← eta_eq_physicalHeight_on_herzogDomain B e _ hdX] at hheight
  have hzero := branchB_bt_zero_height_identity R i hi hz
  change eta B e (r21 R + i) 0 = r23 R + eta B e i (c2 R - 1) at hzero
  change (eta B e (r21 R + i) 0 : ℤ) = max 0 (rawMinimum B e X) at hheight
  omega

include hB x hsx hbirth haxis in
private theorem branchB_r5_principal_location
    (P0 T0 : ℕ)
    (hcoord : actualPrincipalIndex P.M.base * routingM P.M.base (branchBInactiveReindex R) =
      P0 * routingB P.M.base (branchBInactiveReindex R) +
      T0 * routingC P.M.base (branchBInactiveReindex R))
    (hP : P0 < r31 R) (hT : T0 < r32 R)
    (i : ℕ) (hi : i < r31 R)
    (hz : (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) = 0)
    (hdrop : eta P.M.base (branchBInactiveReindex R) (r21 R + i) 0 <
      eta P.M.base (branchBInactiveReindex R) (r21 R + i - 1) 0) : P0 ≤ i := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  obtain ⟨hmin, hQ⟩ := branchB_high_axisC_bt_zero_principal_minimizer R i hi hz hdrop
  have hf := branchB_r5_principal_bt_candidate R P0 T0 hcoord hP hT i hi
  by_contra hnot
  have hlt : i < P0 := by omega
  rw [if_pos hlt, hQ, hmin] at hf
  have hTeta : eta B e i (c2 R - 1) = r13 R := by
    change (eta B e i (c2 R - 1) : ℤ) = r13 R at hf
    exact_mod_cast hf
  have hzheight := branchB_bt_zero_height_identity R i hi hz
  rw [hTeta] at hzheight
  obtain ⟨_, hdX, _, _⟩ := branchB_r4_bt_geometry R i hi
  have hmono := branchB_r3_eta_row_antitone R 0 0 (r21 R + i) (by simpa using hdX)
  have horigin := (branchB_actualZeroEdgeBirth_axisC_high_seam_origin_inner_notch_final_packet
    R hB x hsx hbirth haxis).2.2.2
  have hj : S.coordinate.j.toNat < c3 R := by
    have hu := haxis.2.2.1
    have hl := haxis.2.1
    change S.coordinate.j < (r13 R : ℤ) + r23 R at hu
    change (r13 R : ℤ) < S.coordinate.j at hl
    have hsum : c3 R = r13 R + r23 R := by
      simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    omega
  have hsum : c3 R = r13 R + r23 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
  rw [Nat.zero_add] at hmono
  change eta B e 0 0 = S.coordinate.j.toNat at horigin
  have hbound : eta B e (r21 R + i) 0 < c3 R :=
    lt_of_le_of_lt hmono (horigin.symm ▸ hj)
  have heq : eta B e (r21 R + i) 0 = c3 R := by
    simpa only [hsum, Nat.add_comm] using hzheight
  exact (Nat.ne_of_lt hbound) heq

include hB x hsx hbirth haxis in
/-- Math-R5: the actual live exceptional B-run has no early BT zero.
No endpoint=kappa2, owner persistence or minimizer uniqueness is used. -/
theorem branchB_high_axisC_bt_corridor_positive :
    ∀ i, i < r31 R → 0 < (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R) i (c2 R - 1)) := by
  classical
  let B := P.M.base
  let e := branchBInactiveReindex R
  let G := routingData B e
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  intro t ht
  by_contra hnot
  change ¬ 0 < G.v (gridResidue B e t (c2 R - 1)) at hnot
  have hex : ∃ i, i < r31 R ∧ G.v (gridResidue B e i (c2 R - 1)) = 0 :=
    ⟨t, ht, Nat.eq_zero_of_not_pos hnot⟩
  let i := Nat.find hex
  have hi := (Nat.find_spec hex).1
  have hz := (Nat.find_spec hex).2
  have hfirst : ∀ k < i, 0 < G.v (gridResidue B e k (c2 R - 1)) := by
    intro k hk
    have hno := Nat.find_min hex hk
    have hklt : k < r31 R := by change i < r31 R at hi; omega
    have hne : G.v (gridResidue B e k (c2 R - 1)) ≠ 0 := by
      intro heq; exact hno ⟨hklt, heq⟩
    exact Nat.pos_of_ne_zero hne
  have hdrop := branchB_high_axisC_first_bt_zero_strict_drop R hB x hsx hbirth haxis
    i hi hz hfirst
  obtain ⟨P0, T0, hcoord, hP, hT⟩ :=
    branchB_high_axisC_principal_coordinate_packet R hB x hsx hbirth haxis
  have hcomp := branchB_high_axisC_complementary_principal_coordinate_bound
    R hB x hsx hbirth haxis P0 T0 hcoord hP hT
  have hloc := branchB_r5_principal_location R hB x hsx hbirth haxis
    P0 T0 hcoord hP hT i hi hz hdrop
  have hsel := branchB_high_axisC_bt_zero_selected_location R hB x hsx hbirth haxis i hi hz
  change r31 R ≤ P0 + S.depth at hcomp
  change i < r31 R - S.depth at hsel
  omega

end B72Packet

/- B73 / Math-R6: identify the actual B endpoint by its first zero.
R1--R5 and the frozen B65 production source are unchanged. -/
private theorem branchB_r6_kappa2_b_eq_yminus
    (R : SectorBCriticalRoleBranchB P) :
    (routingData P.M.base (branchBInactiveReindex R)).b
      (gridResidue P.M.base (branchBInactiveReindex R) (r31 R - 1) (c2 R - 1)) =
    gridResidue P.M.base (branchBInactiveReindex R) 0 (r12 R - 1) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  have hp : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hsum : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hrel : c3 R * a = r31 R * b + r32 R * c := by
    change c3 R * routingA P.M.base (branchBInactiveReindex R) =
      r31 R * routingB P.M.base (branchBInactiveReindex R) +
      r32 R * routingC P.M.base (branchBInactiveReindex R)
    rw [branchB_inactive_routingA_eq_normalizedC,
      branchB_inactive_routingB_eq_normalizedA,
      branchB_inactive_routingC_eq_normalizedB]
    simpa using (branchB_actual_herzog_coordinates R).normalized_relations.2.2
  have hcoord : (c2 R - 1) = r32 R + (r12 R - 1) := by omega
  have heq : (r31 R - 1) * b + (c2 R - 1) * c + b =
      (r12 R - 1) * c + c3 R * a := by
    rw [hcoord, hrel]
    nlinarith only [congrArg (fun n => n * b) (Nat.sub_add_cancel (by omega : 1 ≤ r31 R))]
  have hcast := congrArg (fun n : ℕ => (n : ZMod a)) heq
  push_cast at hcast
  rw [show (a : ZMod a) = 0 from ZMod.natCast_self a, mul_zero, add_zero] at hcast
  change gridResidue B e (r31 R - 1) (c2 R - 1) + b = gridResidue B e 0 (r12 R - 1)
  simpa only [gridResidue, Nat.cast_zero, zero_mul, zero_add] using hcast

section B73Packet
variable (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
  (x : BranchBActualExceptionalBranches P R)
  (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
    (actualPrincipalIndex P.M.base) (branchBActualExceptionalNormalizedSource P R x).val)
  (hbirth : IsActualZeroEdgeBirth R x hsx)
  (haxis :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
    S.coordinate.j < qH R + vH R ∧ S.beta = S.coordinate.j * normalizedC R ∧
    (S.n : ℤ) + normalizedA R * S.depth = S.coordinate.j * normalizedC R)

include hB x hsx hbirth haxis in
private theorem branchB_r6_yminus_actual_v_zero :
    (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R) 0 (r12 R - 1)) = 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  have pos := (branchB_actual_herzog_coordinates R).cross_positive
  have hp : 0 < r31 R := by simpa using pos.2.2.2.2.1
  have hq : 0 < r32 R := by simpa using pos.2.2.2.2.2
  have hr : 0 < r12 R := by simpa using pos.1
  have sum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have sum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hdM := branchB_r4_domain R 0 (r12 R - 1) (by omega) (by omega) (Or.inl hp)
  have hdY := branchB_r4_domain R 0 (r12 R) (by omega) (by omega) (Or.inl hp)
  have hstep := branchB_r3_final_c_step R (gridResidue B e 0 (r12 R - 1))
  have hres : gridResidue B e 0 (r12 R - 1) + routingC B e =
      gridResidue B e 0 (r12 R) := by
    rw [← gridResidue_add_c, Nat.sub_add_cancel (by omega : 1 ≤ r12 R)]
  rw [hres, branchB_high_axisC_yminus_ambient_c_carry_zero R,
    ← eta_eq_physicalHeight_on_herzogDomain B e _ hdM,
    ← eta_eq_physicalHeight_on_herzogDomain B e _ hdY] at hstep
  have heq := (branchB_high_axisC_gate_clamp R hB x hsx hbirth haxis).1
  change eta B e 0 (r12 R - 1) = eta B e 0 (r12 R) at heq
  change eta B e 0 (r12 R - 1) + 0 = eta B e 0 (r12 R) +
    (routingData B e).v (gridResidue B e 0 (r12 R - 1)) at hstep
  rw [heq] at hstep
  exact (Nat.add_left_cancel hstep).symm

include hB x hsx hbirth haxis in
private theorem branchB_r6_bFirstZeroIndex_eq_terminal :
    letI : NeZero (routingA P.M.base (branchBInactiveReindex R)) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base (branchBInactiveReindex R))⟩
    L5A2C4I.ResidueData.bFirstZeroIndex
      (routingData P.M.base (branchBInactiveReindex R)) x.val.val = c1 R + 1 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let G := routingData B e
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let A := gridResidue B e (r31 R - 1) (r32 R - 1)
  let N := c1 R + 1
  let n0 := L5A2C4I.ResidueData.bFirstZeroIndex G x.val.val
  have hp : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have sum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hbase : x.val.val.val = A :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_base_eq_inner_notch R hB x hsx hbirth haxis
  have hBN (t : ℕ) : (G.b ^ (t + 1)) A =
      gridResidue B e (r31 R + t) (r32 R - 1) := by
    rw [branchB_r5_b_pow_grid]
    congr 1 <;> omega
  have hBT (t : ℕ) : (G.b ^ (r21 R + 1 + t)) A =
      gridResidue B e t (c2 R - 1) := by
    rw [branchB_r5_b_pow_grid]
    have hcoord : r31 R - 1 + (r21 R + 1 + t) = c1 R + t := by omega
    rw [hcoord, branchB_r5_bn_bt_wrap]
  have hpositive : ∀ k, 0 < k → k < N → 0 < G.v ((G.b ^ k) A) := by
    intro k hk hkn
    by_cases hBNk : k ≤ r21 R
    · have heq : k = (k - 1) + 1 := by omega
      rw [heq, hBN]
      exact branchB_high_axisC_bn_corridor_positive R hB x hsx hbirth haxis (k - 1) (by omega)
    · have heq : k = r21 R + 1 + (k - (r21 R + 1)) := by omega
      rw [heq, hBT]
      exact branchB_high_axisC_bt_corridor_positive R hB x hsx hbirth haxis
        (k - (r21 R + 1)) (by dsimp [N] at hkn; omega)
  have hterminal : (G.b ^ N) A = gridResidue B e 0 (r12 R - 1) := by
    have hN : N = (r21 R + 1 + (r31 R - 1)) + 1 := by dsimp [N]; omega
    rw [hN, pow_succ']
    change G.b ((G.b ^ (r21 R + 1 + (r31 R - 1))) A) = _
    rw [hBT]
    exact branchB_r6_kappa2_b_eq_yminus R
  have hzero : G.v ((G.b ^ N) A) = 0 := by
    rw [hterminal]
    exact branchB_r6_yminus_actual_v_zero R hB x hsx hbirth haxis
  have hn0pos := L5A2C4I.ResidueData.firstZeroIndex_pos G.b G.v
    x.val.val.val x.val.val.property.1.2
  have hn0zero := L5A2C4I.ResidueData.firstZeroIndex_zero G.b G.v
    x.val.val.val x.val.val.property.1.2
  change 0 < n0 at hn0pos
  change G.v ((G.b ^ n0) x.val.val.val) = 0 at hn0zero
  change n0 = N
  apply le_antisymm
  · by_contra h
    have hl : N < n0 := by omega
    have hpos := L5A2C4I.ResidueData.firstZeroIndex_positive_before G.b G.v
      x.val.val.val x.val.val.property.1.2 (by dsimp [N]; omega) hl
    rw [hbase] at hpos
    exact (Nat.ne_of_gt hpos) hzero
  · by_contra h
    have hl : n0 < N := by omega
    have hpos := hpositive n0 hn0pos hl
    rw [hbase] at hn0zero
    exact (Nat.ne_of_gt hpos) hn0zero

include hB x hsx hbirth haxis in
/-- Math-R6: the actual B-run's positive predecessor of its first zero is
kappa2. The terminal zero is derived internally from the frozen B65 clamp. -/
theorem branchB_high_axisC_canonicalBEndpoint_eq_kappa2 :
    letI : NeZero (routingA P.M.base (branchBInactiveReindex R)) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base (branchBInactiveReindex R))⟩
    L5A2C4I.ResidueData.canonicalBEndpoint
      (routingData P.M.base (branchBInactiveReindex R)) x.val.val =
    gridResidue P.M.base (branchBInactiveReindex R) (r31 R - 1) (c2 R - 1) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let G := routingData B e
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hp : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have sum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hfirst := branchB_r6_bFirstZeroIndex_eq_terminal R hB x hsx hbirth haxis
  have hbase := branchB_actualZeroEdgeBirth_axisC_high_seam_base_eq_inner_notch
    R hB x hsx hbirth haxis
  change (G.b ^ (L5A2C4I.ResidueData.bFirstZeroIndex G x.val.val - 1)) x.val.val.val = _
  rw [hfirst, Nat.add_sub_cancel, hbase, branchB_r5_b_pow_grid]
  have hcoord : r31 R - 1 + c1 R = c1 R + (r31 R - 1) := by omega
  rw [hcoord, branchB_r5_bn_bt_wrap]

end B73Packet

/- B74 / Math-R7--R8: direct transverse zero at the same actual B endpoint. -/
private theorem branchB_r7_kappa2_c_eq_x2 (R : SectorBCriticalRoleBranchB P) :
    (routingData P.M.base (branchBInactiveReindex R)).c
      (gridResidue P.M.base (branchBInactiveReindex R) (r31 R - 1) (c2 R - 1)) =
    gridResidue P.M.base (branchBInactiveReindex R) (c1 R - 1) 0 := by
  have hp : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hsum : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hg := (branchB_r4_bt_geometry R (r31 R - 1) (by omega)).2.2.1
  have hcoord : r21 R + (r31 R - 1) = c1 R - 1 := by omega
  rw [hcoord] at hg
  exact hg

private theorem branchB_r7_x2_b_eq_y2 (R : SectorBCriticalRoleBranchB P) :
    (routingData P.M.base (branchBInactiveReindex R)).b
      (gridResidue P.M.base (branchBInactiveReindex R) (c1 R - 1) 0) =
    gridResidue P.M.base (branchBInactiveReindex R) 0 (r12 R) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  have hp : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hsum : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hrel : c1 R * b = r13 R * a + r12 R * c := by
    change c1 R * routingB P.M.base (branchBInactiveReindex R) =
      r13 R * routingA P.M.base (branchBInactiveReindex R) +
      r12 R * routingC P.M.base (branchBInactiveReindex R)
    rw [branchB_inactive_routingA_eq_normalizedC,
      branchB_inactive_routingB_eq_normalizedA,
      branchB_inactive_routingC_eq_normalizedB]
    simpa only [qH, add_comm] using (branchB_actual_herzog_coordinates R).normalized_relations.1
  have heq : (c1 R - 1) * b + b = r12 R * c + r13 R * a := by
    nlinarith only [hrel, congrArg (fun n => n * b)
      (Nat.sub_add_cancel (by omega : 1 ≤ c1 R))]
  have hcast := congrArg (fun n : ℕ => (n : ZMod a)) heq
  push_cast at hcast
  rw [show (a : ZMod a) = 0 from ZMod.natCast_self a, mul_zero, add_zero] at hcast
  change gridResidue B e (c1 R - 1) 0 + b = gridResidue B e 0 (r12 R)
  simpa only [gridResidue, Nat.cast_zero, zero_mul, add_zero, zero_add] using hcast

private theorem branchB_r7_x2_ambient_b_carry_eq_r13
    (R : SectorBCriticalRoleBranchB P) :
    branchBPrefixAmbientU R
      (gridResidue P.M.base (branchBInactiveReindex R) (c1 R - 1) 0) = r13 R := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  have pos := (branchB_actual_herzog_coordinates R).cross_positive
  have hp : 0 < r31 R := by simpa using pos.2.2.2.2.1
  have hq : 0 < r32 R := by simpa using pos.2.2.2.2.2
  have sum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have sum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hdX := branchB_r4_domain R (c1 R - 1) 0 (by omega) (by omega) (Or.inr hq)
  have hdY := branchB_r4_domain R 0 (r12 R) (by omega) (by omega) (Or.inl hp)
  have hs := branchB_inactive_b_carry_spec R (gridResidue B e (c1 R - 1) 0)
  change physicalAlpha B e (gridResidue B e (c1 R - 1) 0) + b =
    physicalAlpha B e (gridResidue B e (c1 R - 1) 0 + b) +
      (a : ℤ) * branchBPrefixAmbientU R (gridResidue B e (c1 R - 1) 0) at hs
  have hres := branchB_r7_x2_b_eq_y2 R
  change gridResidue B e (c1 R - 1) 0 + b = gridResidue B e 0 (r12 R) at hres
  rw [hres, branchB_r4_alpha_grid R _ _ hdX, branchB_r4_alpha_grid R _ _ hdY] at hs
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add] at hs
  have hrel : c1 R * b = r13 R * a + r12 R * c := by
    change c1 R * routingB P.M.base (branchBInactiveReindex R) =
      r13 R * routingA P.M.base (branchBInactiveReindex R) +
      r12 R * routingC P.M.base (branchBInactiveReindex R)
    rw [branchB_inactive_routingA_eq_normalizedC,
      branchB_inactive_routingB_eq_normalizedA,
      branchB_inactive_routingC_eq_normalizedB]
    simpa only [qH, add_comm] using (branchB_actual_herzog_coordinates R).normalized_relations.1
  have heq : (c1 R - 1) * b + b = r12 R * c + r13 R * a := by
    nlinarith only [hrel, congrArg (fun n => n * b)
      (Nat.sub_add_cancel (by omega : 1 ≤ c1 R))]
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) heq
  push_cast at hcast
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  have hh : (a : ℤ) * branchBPrefixAmbientU R (gridResidue B e (c1 R - 1) 0) =
      (a : ℤ) * r13 R := by linear_combination hcast - hs
  exact_mod_cast (mul_left_cancel₀ (ne_of_gt ha) hh)

section B74Packet
variable (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
  (x : BranchBActualExceptionalBranches P R)
  (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
    (actualPrincipalIndex P.M.base) (branchBActualExceptionalNormalizedSource P R x).val)
  (hbirth : IsActualZeroEdgeBirth R x hsx)
  (haxis :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
    S.coordinate.j < qH R + vH R ∧ S.beta = S.coordinate.j * normalizedC R ∧
    (S.n : ℤ) + normalizedA R * S.depth = S.coordinate.j * normalizedC R)

include hB x hsx hbirth haxis in
/-- Math-R7: the frozen B65 gate clamp forces actual transverse zero
at the c-successor of the same B endpoint identified by R6. -/
theorem branchB_high_axisC_canonicalBEndpoint_transverse_zero :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let G := routingData B e
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    G.u (G.c (L5A2C4I.ResidueData.canonicalBEndpoint G x.val.val)) = 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let G := routingData B e
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change G.u (G.c (L5A2C4I.ResidueData.canonicalBEndpoint G x.val.val)) = 0
  rw [branchB_high_axisC_canonicalBEndpoint_eq_kappa2 R hB x hsx hbirth haxis,
    branchB_r7_kappa2_c_eq_x2 R]
  have pos := (branchB_actual_herzog_coordinates R).cross_positive
  have hp : 0 < r31 R := by simpa using pos.2.2.2.2.1
  have hq : 0 < r32 R := by simpa using pos.2.2.2.2.2
  have sum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have sum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hdX := branchB_r4_domain R (c1 R - 1) 0 (by omega) (by omega) (Or.inr hq)
  have hdY := branchB_r4_domain R 0 (r12 R) (by omega) (by omega) (Or.inl hp)
  have hs := branchB_r5_final_b_step R (gridResidue B e (c1 R - 1) 0)
  have hres := branchB_r7_x2_b_eq_y2 R
  change gridResidue B e (c1 R - 1) 0 + routingB B e = gridResidue B e 0 (r12 R) at hres
  rw [hres, branchB_r7_x2_ambient_b_carry_eq_r13 R,
    ← eta_eq_physicalHeight_on_herzogDomain B e _ hdX,
    ← eta_eq_physicalHeight_on_herzogDomain B e _ hdY] at hs
  change eta B e (c1 R - 1) 0 + r13 R = eta B e 0 (r12 R) +
    G.u (gridResidue B e (c1 R - 1) 0) at hs
  have heq := (branchB_high_axisC_gate_clamp R hB x hsx hbirth haxis).2
  change eta B e 0 (r12 R) = eta B e (c1 R - 1) 0 + r13 R at heq
  rw [← heq] at hs
  exact (Nat.add_left_cancel (show eta B e 0 (r12 R) + 0 =
    eta B e 0 (r12 R) + G.u (gridResidue B e (c1 R - 1) 0) by simpa using hs)).symm

include hB x hsx hbirth haxis in
/-- Math-R8: direct local contradiction with the unchanged live B-exceptional
field. This is not an upper Sector-B integration theorem. -/
theorem branchB_high_axisC_actual_B_exceptional_impossible : False := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let G := routingData B e
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hnonex : L5A2C4I.ResidueData.BFirstStageNonexceptional G x.val.val :=
    branchB_high_axisC_canonicalBEndpoint_transverse_zero R hB x hsx hbirth haxis
  exact x.val.property hnonex

end B74Packet

/-! B75: pure upper assembly of the accepted B74 leaf. -/

/-- The weaker axis leaf in the existing event classifier already supplies
the full R8 packet via the frozen anchor coordinate and depth identities. -/
theorem branchB_actualZeroEdgeBirth_high_axisC_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hsx
    ¬ (A.coordinate.i = 0 ∧ qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hsx
  change ¬ (A.coordinate.i = 0 ∧ qH R < A.coordinate.j ∧
    A.coordinate.j < qH R + vH R)
  intro haxis
  have hbeta := A.coordinate.exact_eq
  rw [branchB_selected_return_anchor_level_zero R hB hsx, haxis.1] at hbeta
  simp only [zero_mul, zero_add] at hbeta
  exact branchB_high_axisC_actual_B_exceptional_impossible R hB x hsx hbirth
    ⟨haxis.1, haxis.2.1, haxis.2.2, hbeta, A.anchor_eq.symm.trans hbeta⟩

/-- The first genuine event parent: B74 discharges the sole axis leaf of
the existing strict-arm/high-axis classifier. Actual source minimality and
the chosen support route are retained without extra depth assumptions. -/
theorem branchB_actualZeroEdgeBirth_strict_arm
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hsx
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
    (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (branchBActualExceptionalNormalizedSource P R x).val ∧
    ∃ route, ActualSourceSupportRoute.Matches route
      C.data.sourceX C.data.sourceY C.data.sourceZ ∧
      ((∃ sigma tau : ℕ,
        A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R) ∨
       (∃ sigma tau : ℕ,
        A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R)) := by
  obtain ⟨hmin, route, hroute, hRB | hLT | haxis⟩ :=
    branchB_actualZeroEdgeBirth_strict_arm_or_axisC_seam R hB x hsx hbirth
  · exact ⟨hmin, route, hroute, Or.inl hRB⟩
  · exact ⟨hmin, route, hroute, Or.inr hLT⟩
  · exact (branchB_actualZeroEdgeBirth_high_axisC_impossible
      R hB x hsx hbirth haxis).elim

/-- One further purely logical parent assembly. TARGET principal equality
and same-base OLD remain legal; only genuine zero-edge BIRTH is refined. -/
theorem branchB_actualExceptional_principal_or_old_or_strict_arm
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R) :
    let s := branchBActualExceptionalNormalizedSource P R x
    s.val = (actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) ∨
    ∃ hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base) s.val,
      IsOldActualBranch R x hs ∨
        (IsActualZeroEdgeBirth R x hs ∧
          let A := branchB_actual_selected_return_anchor_v2 R hB hs
          ((∃ sigma tau : ℕ,
            A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
            1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R) ∨
           (∃ sigma tau : ℕ,
            A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
            1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R))) := by
  rcases branchB_actualExceptional_principal_or_principalSurgery_channel P R x
      with htarget | ⟨hs, hold | hbirth⟩
  · exact Or.inl htarget
  · exact Or.inr ⟨hs, Or.inl hold⟩
  · obtain ⟨_, _, _, harm⟩ := branchB_actualZeroEdgeBirth_strict_arm R hB x hs hbirth
    exact Or.inr ⟨hs, Or.inr ⟨hbirth, harm⟩⟩

/-- B76: the selected anchor is the ambient Apéry representative at its own level.
This uses the original selected-anchor pivot, not the inactive routing pivot. -/
theorem branchB_selected_return_beta_eq_alpha_n
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    letI : NeZero (normalizedA R) := ⟨(branchB_actual_normalizedA_pos R).ne'⟩
    A.beta = (normalizedH P.M.base).asRelativeIdeal.aperyRepresentative
      (normalizedA R) (A.n : ZMod (normalizedA R)) := by
  rfl

/-- B76: the natural defect in the exact normal-form equation is unique. -/
theorem branchB_selected_return_defect_unique
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (d : ℕ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    A.beta = A.n + normalizedA R * d ↔ d = A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.beta = (A.n : ℤ) + (normalizedA R : ℤ) * d ↔ d = A.depth
  have ha : (0 : ℤ) < normalizedA R := by
    exact_mod_cast branchB_actual_normalizedA_pos R
  constructor
  · intro h
    have hm : (normalizedA R : ℤ) * d = (normalizedA R : ℤ) * A.depth := by
      rw [A.anchor_eq] at h
      linarith
    have hd := mul_left_cancel₀ (ne_of_gt ha) hm
    exact_mod_cast hd
  · intro hd
    rw [hd]
    exact A.anchor_eq

/-- B76: a quotient dictionary for the same actual selected-anchor defect. -/
theorem branchB_selected_return_depth_eq_defect_quotient
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    ((A.beta - A.n) / normalizedA R : ℤ) = A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change ((A.beta - (A.n : ℤ)) / (normalizedA R : ℤ)) = (A.depth : ℤ)
  have ha : (0 : ℤ) < normalizedA R := by
    exact_mod_cast branchB_actual_normalizedA_pos R
  rw [A.anchor_eq]
  rw [add_sub_cancel_left]
  exact Int.mul_ediv_cancel_left _ ha.ne'

end NS25Lean.L5A2B4AR5B
