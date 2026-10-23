import NS25Lean.P2PrefixDictionary
import NS25Lean.P2BranchARectangleLocalization

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2BFinalRepair

open ChosenBase FourGeneratedBridge L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR4R2A L5A2B4AR5A L5A2C4H L5A2C4OR3 L5A2C4OR4
open L5A2C4C
open L5A2B4AR3

variable {Gamma H : NumericalSemigroup} {P : P2Data Gamma}

/-- The prefix is an honest relative ideal as soon as there is a strict
positive return level. No event, ENTRY, or provenance selector is required. -/
def principalPrefixIdeal (H : NumericalSemigroup) (m Q : ℕ) (hQ : 1 < Q) :
    RelativeIdeal H where
  carrier := prefixCarrier H m Q
  nonempty := by
    obtain ⟨z, hz⟩ := (returnIdeal H m).nonempty
    exact ⟨z, 1, by omega, hQ, by simpa using hz⟩
  bddBelow := by
    obtain ⟨z, hz⟩ := H.asRelativeIdeal.bddBelow
    exact ⟨z, fun _ ⟨_, _, _, hw⟩ => hz hw.1⟩
  add_mem := by
    rintro z t ⟨ell, hp, hl, hz⟩ ht
    exact ⟨ell, hp, hl, (returnIdeal H (ell*m)).add_mem hz ht⟩

theorem principal_not_mem_prefix (H : NumericalSemigroup) (m : ℕ) (hm : 0 < m) :
    ((principalIndex H m hm * m : ℕ) : ℤ) ∉
      prefixCarrier H m (principalIndex H m hm) := by
  let Q := principalIndex H m hm
  rintro ⟨ell, hp, hl, _, hret⟩
  have hkpos : 0 < Q-ell := by omega
  have hklt : Q-ell < Q := by omega
  have he : ((Q*m : ℕ) : ℤ) - (ell*m : ℕ) = ((Q-ell)*m : ℕ) := by
    rw [Nat.sub_mul, Nat.cast_sub (Nat.mul_le_mul_right m (by omega : ell ≤ Q))]
  have hk : (Q-ell)*m ∈ H := by
    change ((Q*m : ℕ) : ℤ) - (ell*m : ℕ) ∈ H.asRelativeIdeal at hret
    rw [he] at hret
    obtain ⟨t, ht, heq⟩ := hret
    have heq' : (Q-ell)*m = t := by exact_mod_cast heq
    exact heq' ▸ ht
  exact (Nat.not_le_of_gt hklt) (principalIndex_min H m hm hkpos hk)

/-- Actual colon membership, restricted to the tail ring's semigroup. -/
def principalColonCarrier (H : NumericalSemigroup) (m Q : ℕ) : Set ℤ :=
  {h | h ∈ H.asRelativeIdeal ∧ (Q*m : ℕ) + h ∈ prefixCarrier H m Q}

theorem principal_colon_cyclic_reverse (H : NumericalSemigroup) (m Q : ℕ)
    (hf : Q*m ∈ H) (h : ℤ) :
    h ∈ principalColonCarrier H m Q ↔
      h ∈ H.asRelativeIdeal ∧
        ∃ ell : ℕ, 0 < ell ∧ ell < Q ∧ h + (ell*m : ℕ) ∈ H.asRelativeIdeal := by
  have hfZ : ((Q*m : ℕ) : ℤ) ∈ H.asRelativeIdeal := ⟨Q*m, hf, rfl⟩
  constructor
  · rintro ⟨hh, ell, hp, hl, _, hret⟩
    refine ⟨hh, Q-ell, by omega, by omega, ?_⟩
    have he : ((Q*m : ℕ) : ℤ) + h - (ell*m : ℕ) = h + ((Q-ell)*m : ℕ) := by
      rw [Nat.sub_mul, Nat.cast_sub (Nat.mul_le_mul_right m (by omega : ell ≤ Q))]
      ring
    change ((Q*m : ℕ) : ℤ) + h - (ell*m : ℕ) ∈ H.asRelativeIdeal at hret
    exact he ▸ hret
  · rintro ⟨hh, ell, hp, hl, hret⟩
    have hsum : ((Q*m : ℕ) : ℤ) + h ∈ H.asRelativeIdeal := by
      obtain ⟨t, ht, rfl⟩ := hh
      exact H.asRelativeIdeal.add_mem hfZ ht
    refine ⟨hh, Q-ell, by omega, by omega, hsum, ?_⟩
    have he : ((Q*m : ℕ) : ℤ) + h - ((Q-ell)*m : ℕ) = h + (ell*m : ℕ) := by
      rw [Nat.sub_mul, Nat.cast_sub (Nat.mul_le_mul_right m (by omega : ell ≤ Q))]
      ring
    change ((Q*m : ℕ) : ℤ) + h - ((Q-ell)*m : ℕ) ∈ H.asRelativeIdeal
    exact he.symm ▸ hret

theorem principal_is_new_source (H : NumericalSemigroup) (m : ℕ) (hm : 0 < m) :
    IsSource H (finalCarrier H m (principalIndex H m hm))
      (principalIndex H m hm * m : ℕ) := by
  let Q := principalIndex H m hm
  refine ⟨Or.inr (by change _ - _ ∈ H.asRelativeIdeal; exact ⟨0, H.zero_mem, by simp⟩), ?_⟩
  intro t ht ht0 hsub
  rcases hsub with hprefix | hprincipal
  · apply principal_not_mem_prefix H m hm
    obtain ⟨ell, hp, hl, hz⟩ := hprefix
    have hmem := (returnIdeal H (ell*m)).add_mem hz ht
    have he : ((Q*m : ℕ) : ℤ) - t + t = (Q*m : ℕ) := by ring
    exact ⟨ell, hp, hl, he ▸ hmem⟩
  · obtain ⟨n, _, hn⟩ := hprincipal
    omega

/-- Normalized CI gluing coefficients: V is the b-coordinate reduced modulo h.
This definition permits zero U and V; positivity is never a definition. -/
abbrev ciG (A : SectorBCriticalRoleBranchA P) := d A
abbrev ciH (A : SectorBCriticalRoleBranchA P) := alpha A
abbrev ciK (A : SectorBCriticalRoleBranchA P) := beta A
abbrev ciU (A : SectorBCriticalRoleBranchA P) := r A + (s A / alpha A) * beta A
abbrev ciV (A : SectorBCriticalRoleBranchA P) := s A % alpha A

theorem symmetric_ci_normalized_equations (A : SectorBCriticalRoleBranchA P) :
    0 < ciG A ∧ 0 < ciH A ∧ 0 < ciK A ∧ ciV A < ciH A ∧
    Nat.Coprime (ciH A) (ciK A) ∧ Nat.Coprime (ciG A) (n2 A) ∧
    n0 A = ciG A * ciH A ∧ n1 A = ciG A * ciK A ∧
    n2 A = ciU A * ciH A + ciV A * ciK A := by
  let S := branchA_symmetricTailData A
  have hg : 0 < d A := Nat.pos_of_ne_zero (fun hz => by have he := S.n0_eq; rw [hz, zero_mul] at he; exact S.n0_pos.ne' he)
  have hh : 0 < alpha A := Nat.pos_of_ne_zero (fun hz => by have he := S.n0_eq; rw [hz, mul_zero] at he; exact S.n0_pos.ne' he)
  have hk : 0 < beta A := Nat.pos_of_ne_zero (fun hz => by have he := S.n1_eq; rw [hz, mul_zero] at he; exact S.n1_pos.ne' he)
  refine ⟨hg, hh, hk, Nat.mod_lt _ hh, S.alpha_beta_coprime, S.d_n2_coprime,
    S.n0_eq, S.n1_eq, ?_⟩
  rw [S.n2_eq]
  have he := Nat.mod_add_div (s A) (alpha A)
  dsimp [ciU, ciV]
  calc
    r A * alpha A + s A * beta A =
        r A * alpha A + (s A % alpha A + alpha A * (s A / alpha A)) * beta A := by rw [he]
    _ = (r A + s A / alpha A * beta A) * alpha A + s A % alpha A * beta A := by ring

theorem symmetric_ci_rectangle_canonical (A : SectorBCriticalRoleBranchA P)
    {i j : ℕ} (hi : i < ciH A) (hj : j < ciG A) :
    IsCanonicalTailGridPoint P.M.base A.reindex i j :=
  branchA_rectangle_canonicality A hi hj

theorem symmetric_ci_b_carry (A : SectorBCriticalRoleBranchA P) :
    ciH A * n1 A = ciK A * n0 A :=
  (branchA_symmetricTailData A).pure_relation.symm

theorem symmetric_ci_c_carry (A : SectorBCriticalRoleBranchA P) (i : ℕ) :
    i * n1 A + ciG A * n2 A =
      ((i + ciV A) % ciH A) * n1 A +
        (ciU A + ((i + ciV A) / ciH A) * ciK A) * n0 A := by
  have S := symmetric_ci_normalized_equations A
  have hpure := symmetric_ci_b_carry A
  have hmixed : ciG A * n2 A = ciU A * n0 A + ciV A * n1 A := by
    rw [S.2.2.2.2.2.2.1, S.2.2.2.2.2.2.2.1, S.2.2.2.2.2.2.2.2]
    ring
  rw [hmixed]
  have he := Nat.mod_add_div (i+ciV A) (ciH A)
  calc
    i * n1 A + (ciU A * n0 A + ciV A * n1 A) =
        (i + ciV A) * n1 A + ciU A * n0 A := by ring
    _ = ((i + ciV A) % ciH A + ciH A * ((i + ciV A) / ciH A)) * n1 A +
        ciU A * n0 A := by rw [he]
    _ = ((i + ciV A) % ciH A) * n1 A +
        (ciU A + ((i + ciV A) / ciH A) * ciK A) * n0 A := by
      calc
        _ = ((i + ciV A) % ciH A) * n1 A +
            ((i + ciV A) / ciH A) * (ciH A * n1 A) + ciU A * n0 A := by ring
        _ = _ := by rw [hpure]; ring

private theorem ci_grid_mem (A : SectorBCriticalRoleBranchA P) (p q t : ℕ) :
    ((p*n0 A + q*n1 A + t*n2 A : ℕ) : ℤ) ∈
      (routingH P.M.base A.reindex).asRelativeIdeal := by
  refine ⟨_, ?_, rfl⟩
  change _ ∈ generatedThree (routingA P.M.base A.reindex)
    (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
  rw [routingA_eq_n0 A, routingB_eq_n1 A, routingC_eq_n2 A]
  exact (mem_generatedThree_iff _ _ _ _).mpr ⟨p,q,t,rfl⟩

private theorem nat_mem_of_int_mem {H : NumericalSemigroup} {n : ℕ}
    (hn : (n : ℤ) ∈ H.asRelativeIdeal) : n ∈ H := by
  obtain ⟨u, hu, he⟩ := hn
  have he' : n=u := by exact_mod_cast he
  exact he' ▸ hu

theorem symmetric_returnIdeal_le_final (A : SectorBCriticalRoleBranchA P)
    {ell : ℕ} (hp : 0 < ell) {z : ℤ}
    (hz : z ∈ returnIdeal (routingH P.M.base A.reindex) (ell*normalizedM P.M.base)) :
    z ∈ routingI P.M.base A.reindex := by
  apply (mem_normalizedTailIdeal_iff_positive_return
    (L5A2C4H.chosenBase_minimalFour P.M.base A.reindex) z).mpr
  exact ⟨ell, hp, hz⟩

/-- LIVE is exported as actual final-ideal nonmembership, not as an assumed
admission bound. The original critical fibers supply all three exclusions. -/
theorem symmetric_live_pure_predecessors (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) :
    (((ciK A-1)*n0 A : ℕ) : ℤ) ∉ routingI P.M.base A.reindex ∧
    (((ciH A-1)*n1 A : ℕ) : ℤ) ∉ routingI P.M.base A.reindex ∧
    (((ciG A-1)*n2 A : ℕ) : ℤ) ∉ routingI P.M.base A.reindex := by
  have he := branchA_critical_eta_bounds P hB A
  have S := symmetric_ci_normalized_equations A
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hz' : (normalizedGrid P.M.base A.reindex (ciK A-1) 0 0 : ℤ) ∈
        routingI P.M.base A.reindex := by
      simpa only [normalizedGrid, zero_mul, add_zero, routingA_eq_n0 A] using hz
    have hm := (normalizedGrid_mem_iff_eta_le P.M.base A.reindex (ciK A-1) 0 0).mp hz'
    have hk := S.2.2.1
    have hb := he.1
    change 0 < beta A at hk
    change eta P.M.base A.reindex 0 0 ≤ beta A-1 at hm
    omega
  · intro hz
    have hz' : (normalizedGrid P.M.base A.reindex 0 (ciH A-1) 0 : ℤ) ∈
        routingI P.M.base A.reindex := by
      simpa only [normalizedGrid, zero_mul, zero_add, add_zero, routingB_eq_n1 A] using hz
    have hm := (normalizedGrid_mem_iff_eta_le P.M.base A.reindex 0 (ciH A-1) 0).mp hz'
    have hb := he.2.1
    change eta P.M.base A.reindex (alpha A-1) 0 ≤ 0 at hm
    omega
  · intro hz
    have hz' : (normalizedGrid P.M.base A.reindex 0 0 (ciG A-1) : ℤ) ∈
        routingI P.M.base A.reindex := by
      simpa only [normalizedGrid, zero_mul, zero_add, routingC_eq_n2 A] using hz
    have hm := (normalizedGrid_mem_iff_eta_le P.M.base A.reindex 0 0 (ciG A-1)).mp hz'
    have hb := he.2.2.2.2
    change eta P.M.base A.reindex 0 (d A-1) ≤ 0 at hm
    omega

private theorem ci_axis_not_mem_return (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {ell t : ℕ} (hp : 0 < ell) :
    (t < ciH A → ((t*n1 A : ℕ) : ℤ) ∉
      returnIdeal (routingH P.M.base A.reindex) (ell*normalizedM P.M.base)) ∧
    (t < ciG A → ((t*n2 A : ℕ) : ℤ) ∉
      returnIdeal (routingH P.M.base A.reindex) (ell*normalizedM P.M.base)) := by
  have he := symmetric_live_pure_predecessors A hB
  constructor
  · intro ht hz
    have hm := symmetric_returnIdeal_le_final A hp hz
    have hdelta : (ciH A-1-t)*n1 A ∈ routingH P.M.base A.reindex := by
      have h := nat_mem_of_int_mem (ci_grid_mem A 0 (ciH A-1-t) 0)
      simpa only [zero_mul, zero_add, add_zero] using h
    have hs := (routingI P.M.base A.reindex).add_mem hm hdelta
    have hsum : (t*n1 A : ℤ) + ((ciH A-1-t)*n1 A : ℕ) = ((ciH A-1)*n1 A : ℕ) := by
      have h : t+(ciH A-1-t) = ciH A-1 := by omega
      exact_mod_cast (show t*n1 A+(ciH A-1-t)*n1 A = (ciH A-1)*n1 A by rw [← add_mul,h])
    exact he.2.1 (hsum ▸ hs)
  · intro ht hz
    have hm := symmetric_returnIdeal_le_final A hp hz
    have hdelta : (ciG A-1-t)*n2 A ∈ routingH P.M.base A.reindex := by
      have h := nat_mem_of_int_mem (ci_grid_mem A 0 0 (ciG A-1-t))
      simpa only [zero_mul, zero_add] using h
    have hs := (routingI P.M.base A.reindex).add_mem hm hdelta
    have hsum : (t*n2 A : ℤ) + ((ciG A-1-t)*n2 A : ℕ) = ((ciG A-1)*n2 A : ℕ) := by
      have h : t+(ciG A-1-t) = ciG A-1 := by omega
      exact_mod_cast (show t*n2 A+(ciG A-1-t)*n2 A = (ciG A-1)*n2 A by rw [← add_mul,h])
    exact he.2.2 (hsum ▸ hs)

/-- Admission follows from LIVE and exact anchor balance. Neither positive
anchor coordinates nor either depth upper bound is an input. -/
theorem symmetric_single_return_admission (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {ell i j depth : ℕ} (hp : 0 < ell)
    (hi : i < ciH A) (hj : j < ciG A)
    (hb : i*n1 A+j*n2 A = ell*normalizedM P.M.base+depth*n0 A) :
    0 < i ∧ 0 < j ∧ depth < ciK A ∧
      depth < ciU A + ((i+ciV A)/ciH A)*ciK A := by
  let HH := routingH P.M.base A.reindex
  let n := ell*normalizedM P.M.base
  have hF : ((i*n1 A+j*n2 A : ℕ) : ℤ) ∈ returnIdeal HH n := by
    refine ⟨by simpa only [zero_mul, zero_add] using ci_grid_mem A 0 i j, ?_⟩
    change _ - (n : ℤ) ∈ HH.asRelativeIdeal
    have he : ((i*n1 A+j*n2 A : ℕ) : ℤ)-(n : ℕ) = (depth*n0 A : ℕ) := by
      have he' : ((i*n1 A+j*n2 A : ℕ) : ℤ) = (n : ℕ) + (depth*n0 A : ℕ) := by exact_mod_cast hb
      omega
    rw [he]
    simpa only [zero_mul, add_zero] using ci_grid_mem A depth 0 0
  have hiP : 0 < i := by
    by_contra hn
    have hz : i=0 := by omega
    apply (ci_axis_not_mem_return A hB hp).2 hj
    simpa [hz, n, HH] using hF
  have hjP : 0 < j := by
    by_contra hn
    have hz : j=0 := by omega
    apply (ci_axis_not_mem_return A hB hp).1 hi
    simpa [hz, n, HH] using hF
  have hdk : depth < ciK A := by
    by_contra hn
    apply (ci_axis_not_mem_return A hB hp).2 hj
    refine ⟨by simpa only [zero_mul, zero_add] using ci_grid_mem A 0 0 j, ?_⟩
    change ((j*n2 A : ℕ) : ℤ)-(n : ℕ) ∈ HH.asRelativeIdeal
    have he : ((j*n2 A : ℕ) : ℤ)-(n : ℕ) =
        ((depth-ciK A)*n0 A+(ciH A-i)*n1 A : ℕ) := by
      have hr := symmetric_ci_b_carry A
      have hd : depth = depth-ciK A+ciK A := by omega
      have hdi : ciH A = ciH A-i+i := by omega
      have hbZ : (i : ℤ)*n1 A+j*n2 A=n+depth*n0 A := by exact_mod_cast hb
      have hrZ : (ciH A : ℤ)*n1 A=ciK A*n0 A := by exact_mod_cast hr
      have hdZ : (depth : ℤ) = (depth-ciK A : ℕ)+ciK A := by exact_mod_cast hd
      have hiZ : (ciH A : ℤ) = (ciH A-i : ℕ)+i := by exact_mod_cast hdi
      simp only [Nat.cast_add, Nat.cast_mul]
      nlinarith only [hbZ, hrZ, hdZ, hiZ]
    rw [he]
    simpa only [zero_mul, add_zero] using ci_grid_mem A (depth-ciK A) (ciH A-i) 0
  have hdc : depth < ciU A+((i+ciV A)/ciH A)*ciK A := by
    by_contra hn
    let cost := ciU A+((i+ciV A)/ciH A)*ciK A
    let t := (i+ciV A)%ciH A
    have ht : t < ciH A := Nat.mod_lt _ (symmetric_ci_normalized_equations A).2.1
    apply (ci_axis_not_mem_return A hB hp).1 ht
    refine ⟨by simpa only [zero_mul, zero_add, add_zero] using ci_grid_mem A 0 t 0, ?_⟩
    change ((t*n1 A : ℕ) : ℤ)-(n : ℕ) ∈ HH.asRelativeIdeal
    have he : ((t*n1 A : ℕ) : ℤ)-(n : ℕ) =
        ((depth-cost)*n0 A+(ciG A-j)*n2 A : ℕ) := by
      have hr := symmetric_ci_c_carry A i
      have hd : depth=depth-cost+cost := by dsimp [cost]; omega
      have hdj : ciG A=ciG A-j+j := by omega
      have hbZ : (i : ℤ)*n1 A+j*n2 A=n+depth*n0 A := by exact_mod_cast hb
      have hrZ : (i : ℤ)*n1 A+ciG A*n2 A=t*n1 A+cost*n0 A := by exact_mod_cast hr
      have hdZ : (depth : ℤ)=(depth-cost : ℕ)+cost := by exact_mod_cast hd
      have hjZ : (ciG A : ℤ)=(ciG A-j : ℕ)+j := by exact_mod_cast hdj
      simp only [Nat.cast_add, Nat.cast_mul]
      nlinarith only [hbZ, hrZ, hdZ, hjZ]
    rw [he]
    simpa only [zero_mul, zero_add, add_zero] using ci_grid_mem A (depth-cost) 0 (ciG A-j)
  exact ⟨hiP, hjP, hdk, hdc⟩

/-- Signed canonical height detects tail membership exactly. This is the
no-hidden-toric-identification bridge for first-carry proofs. -/
theorem symmetric_ci_signed_height_mem_iff (A : SectorBCriticalRoleBranchA P)
    {i j : ℕ} (hi : i < ciH A) (hj : j < ciG A) (l : ℤ) :
    l*n0 A + i*n1 A+j*n2 A ∈ (routingH P.M.base A.reindex).asRelativeIdeal ↔ 0 ≤ l := by
  let B := P.M.base
  let e := A.reindex
  letI : NeZero (routingA B e) := ⟨(routingA_pos B e).ne'⟩
  have ha : (0 : ℤ) < n0 A := by exact_mod_cast (branchA_symmetricTailData A).n0_pos
  have hc := symmetric_ci_rectangle_canonical A hi hj
  change ((normalizedGrid B e 0 i j : ℕ) : ℤ) = physicalAlpha B e (gridResidue B e i j) at hc
  have hc' : physicalAlpha B e (gridResidue B e i j) = (i : ℤ)*n1 A+j*n2 A := by
    rw [← hc]
    dsimp only [B,e]
    simp only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul,
      routingB_eq_n1 A, routingC_eq_n2 A]
  constructor
  · intro hz
    have hmod : ((l*n0 A+i*n1 A+j*n2 A : ℤ) : ZMod (routingA B e)) = gridResidue B e i j := by
      have hmod' := normalizedGrid_mod B e 0 i j
      simpa only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul,
        Int.cast_add, Int.cast_mul, Int.cast_natCast, ← routingA_eq_n0 A,
        ← routingB_eq_n1 A, ← routingC_eq_n2 A, ZMod.natCast_self, mul_zero, zero_add] using hmod'
    have hle := (routingH B e).asRelativeIdeal.aperyRepresentative_le
      (routingA B e) (gridResidue B e i j) hz hmod
    change physicalAlpha B e (gridResidue B e i j) ≤ _ at hle
    rw [hc'] at hle
    nlinarith
  · intro hl
    have he : l = (l.toNat : ℕ) := (Int.toNat_of_nonneg hl).symm
    rw [he]
    simpa only [Nat.cast_add, Nat.cast_mul] using ci_grid_mem A l.toNat i j

abbrev symmetricF (A : SectorBCriticalRoleBranchA P) (i j : ℕ) := i*n1 A+j*n2 A
abbrev symmetricX (A : SectorBCriticalRoleBranchA P) (j depth : ℕ) :=
  (ciK A-depth)*n0 A+j*n2 A
abbrev symmetricY (A : SectorBCriticalRoleBranchA P) (i depth : ℕ) :=
  (ciU A+((i+ciV A)/ciH A)*ciK A-depth)*n0 A+
    ((i+ciV A)%ciH A)*n1 A

theorem symmetric_single_return_source_differences (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {ell i j depth : ℕ} (hp : 0 < ell)
    (hi : i < ciH A) (hj : j < ciG A)
    (hb : i*n1 A+j*n2 A=ell*normalizedM P.M.base+depth*n0 A) :
    (symmetricF A i j : ℤ)-(ell*normalizedM P.M.base : ℕ)=(depth*n0 A : ℕ) ∧
    (symmetricX A j depth : ℤ)-(ell*normalizedM P.M.base : ℕ)=((ciH A-i)*n1 A : ℕ) ∧
    (symmetricY A i depth : ℤ)-(ell*normalizedM P.M.base : ℕ)=((ciG A-j)*n2 A : ℕ) := by
  have had := symmetric_single_return_admission A hB hp hi hj hb
  have hbZ : (i : ℤ)*n1 A+j*n2 A=(ell*normalizedM P.M.base : ℕ)+depth*n0 A := by exact_mod_cast hb
  simp only [Nat.cast_mul] at hbZ
  refine ⟨by simp only [symmetricF,Nat.cast_add,Nat.cast_mul]; omega, ?_, ?_⟩
  · have hrel : (ciH A : ℤ)*n1 A=ciK A*n0 A := by exact_mod_cast symmetric_ci_b_carry A
    have hd : (ciK A-depth : ℕ)+(depth : ℤ)=ciK A := by exact_mod_cast (Nat.sub_add_cancel (by omega : depth ≤ ciK A))
    have ht : (ciH A-i : ℕ)+(i : ℤ)=ciH A := by exact_mod_cast (Nat.sub_add_cancel (by omega : i ≤ ciH A))
    simp only [symmetricX,Nat.cast_add,Nat.cast_mul]
    nlinarith only [hbZ,hrel,hd,ht]
  · let cost := ciU A+((i+ciV A)/ciH A)*ciK A
    let t := (i+ciV A)%ciH A
    have hrel : (i : ℤ)*n1 A+ciG A*n2 A=t*n1 A+cost*n0 A := by exact_mod_cast symmetric_ci_c_carry A i
    have hd : (cost-depth : ℕ)+(depth : ℤ)=cost := by
      exact_mod_cast (Nat.sub_add_cancel (by dsimp [cost]; omega : depth ≤ cost))
    have ht : (ciG A-j : ℕ)+(j : ℤ)=ciG A := by exact_mod_cast (Nat.sub_add_cancel (by omega : j ≤ ciG A))
    change (((cost-depth)*n0 A+t*n1 A : ℕ) : ℤ)-((ell*normalizedM P.M.base : ℕ) : ℤ)=(((ciG A-j)*n2 A : ℕ) : ℤ)
    simp only [Nat.cast_add,Nat.cast_mul]
    nlinarith only [hbZ,hrel,hd,ht]

private theorem int_ideal_add_mem {H : NumericalSemigroup} (I : RelativeIdeal H)
    {z t : ℤ} (hz : z ∈ I) (ht : t ∈ H.asRelativeIdeal) : z+t ∈ I := by
  obtain ⟨n, hn, rfl⟩ := ht
  exact I.add_mem hz hn

theorem symmetric_single_return_sources_mem (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {ell i j depth : ℕ} (hp : 0 < ell)
    (hi : i < ciH A) (hj : j < ciG A)
    (hb : i*n1 A+j*n2 A=ell*normalizedM P.M.base+depth*n0 A) :
    (symmetricF A i j : ℤ) ∈ returnIdeal (routingH P.M.base A.reindex) (ell*normalizedM P.M.base) ∧
    (symmetricX A j depth : ℤ) ∈ returnIdeal (routingH P.M.base A.reindex) (ell*normalizedM P.M.base) ∧
    (symmetricY A i depth : ℤ) ∈ returnIdeal (routingH P.M.base A.reindex) (ell*normalizedM P.M.base) := by
  have hd := symmetric_single_return_source_differences A hB hp hi hj hb
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · simpa only [zero_mul,zero_add] using ci_grid_mem A 0 i j
  · change (symmetricF A i j : ℤ)-(ell*normalizedM P.M.base : ℕ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal
    rw [hd.1]
    simpa only [zero_mul,add_zero] using ci_grid_mem A depth 0 0
  · simpa only [zero_mul,zero_add,add_zero] using ci_grid_mem A (ciK A-depth) 0 j
  · change (symmetricX A j depth : ℤ)-(ell*normalizedM P.M.base : ℕ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal
    rw [hd.2.1]
    simpa only [zero_mul,zero_add,add_zero] using ci_grid_mem A 0 (ciH A-i) 0
  · simpa only [zero_mul,add_zero] using ci_grid_mem A
      (ciU A+((i+ciV A)/ciH A)*ciK A-depth) ((i+ciV A)%ciH A) 0
  · change (symmetricY A i depth : ℤ)-(ell*normalizedM P.M.base : ℕ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal
    rw [hd.2.2]
    simpa only [zero_mul,zero_add] using ci_grid_mem A 0 0 (ciG A-j)

/-- Exact F/X/Y generation of every individual nonprincipal return ideal.
No minimality or family completeness appears as an input. -/
theorem symmetric_single_return_three_sources (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {ell i j depth : ℕ} (hp : 0 < ell)
    (hi : i < ciH A) (hj : j < ciG A)
    (hb : i*n1 A+j*n2 A=ell*normalizedM P.M.base+depth*n0 A) (z : ℤ) :
    z ∈ returnIdeal (routingH P.M.base A.reindex) (ell*normalizedM P.M.base) ↔
    z-(symmetricF A i j : ℕ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal ∨
    z-(symmetricX A j depth : ℕ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal ∨
    z-(symmetricY A i depth : ℕ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal := by
  let HH := routingH P.M.base A.reindex
  let n := ell*normalizedM P.M.base
  have hdiff := symmetric_single_return_source_differences A hB hp hi hj hb
  constructor
  · rintro ⟨hzH,hret⟩
    change z-(n : ℕ) ∈ HH.asRelativeIdeal at hret
    obtain ⟨w,hw,he⟩ := hret
    obtain ⟨p,q,t,_,_,hf⟩ := branchA_routingH_rectangle_factorization A hw
    rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A] at hf
    have heZ : z=(n : ℕ)+(p : ℤ)*n0 A+q*n1 A+t*n2 A := by
      rw [hf] at he
      simp only [Nat.cast_add,Nat.cast_mul] at he
      omega
    have hbZ : (i : ℤ)*n1 A+j*n2 A=(n : ℕ)+depth*n0 A := by exact_mod_cast hb
    dsimp only [n] at heZ hbZ
    simp only [Nat.cast_mul] at heZ hbZ
    by_cases hpd : depth ≤ p
    · left
      have hd : (p-depth : ℕ)+(depth : ℤ)=p := by exact_mod_cast Nat.sub_add_cancel hpd
      have heq : z-(symmetricF A i j : ℕ)=((p-depth)*n0 A+q*n1 A+t*n2 A : ℕ) := by
        simp only [symmetricF,Nat.cast_add,Nat.cast_mul]
        nlinarith only [heZ,hbZ,hd]
      rw [heq]; exact ci_grid_mem A (p-depth) q t
    by_cases hqb : ciH A-i ≤ q
    · right; left
      have hd : (q-(ciH A-i) : ℕ)+((ciH A-i : ℕ) : ℤ)=q := by exact_mod_cast Nat.sub_add_cancel hqb
      have heq : z-(symmetricX A j depth : ℕ)=
          (p*n0 A+(q-(ciH A-i))*n1 A+t*n2 A : ℕ) := by
        have hx := hdiff.2.1
        simp only [Nat.cast_add,Nat.cast_mul] at hx
        simp only [Nat.cast_add,Nat.cast_mul]
        nlinarith only [heZ,hx,hd]
      rw [heq]; exact ci_grid_mem A p (q-(ciH A-i)) t
    by_cases htc : ciG A-j ≤ t
    · right; right
      have hd : (t-(ciG A-j) : ℕ)+((ciG A-j : ℕ) : ℤ)=t := by exact_mod_cast Nat.sub_add_cancel htc
      have heq : z-(symmetricY A i depth : ℕ)=
          (p*n0 A+q*n1 A+(t-(ciG A-j))*n2 A : ℕ) := by
        have hy := hdiff.2.2
        simp only [Nat.cast_add,Nat.cast_mul] at hy
        simp only [Nat.cast_add,Nat.cast_mul]
        nlinarith only [heZ,hy,hd]
      rw [heq]; exact ci_grid_mem A p q (t-(ciG A-j))
    have hic : i+q < ciH A := by omega
    have hjc : j+t < ciG A := by omega
    have heq : z=((p : ℤ)-depth)*n0 A+(i+q : ℕ)*n1 A+(j+t : ℕ)*n2 A := by
      simp only [Nat.cast_add]
      nlinarith only [heZ,hbZ]
    rw [heq] at hzH
    have hheight := (symmetric_ci_signed_height_mem_iff A hic hjc ((p : ℤ)-depth)).mp hzH
    omega
  · intro hz
    have hm := symmetric_single_return_sources_mem A hB hp hi hj hb
    rcases hz with hz | hz | hz
    · have h := int_ideal_add_mem _ hm.1 hz
      simpa only [add_sub_cancel] using h
    · have h := int_ideal_add_mem _ hm.2.1 hz
      simpa only [add_sub_cancel] using h
    · have h := int_ideal_add_mem _ hm.2.2 hz
      simpa only [add_sub_cancel] using h

theorem symmetric_single_return_colon_threshold (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {ell i j depth x y height : ℕ} (hp : 0 < ell)
    (hi : i < ciH A) (hj : j < ciG A)
    (hb : i*n1 A+j*n2 A=ell*normalizedM P.M.base+depth*n0 A)
    (hx : x < ciH A) (hy : y < ciG A) :
    ((height*n0 A+x*n1 A+y*n2 A+ell*normalizedM P.M.base : ℕ) : ℤ) ∈
      (routingH P.M.base A.reindex).asRelativeIdeal ↔
      depth ≤ height ∨ ciH A-i ≤ x ∨ ciG A-j ≤ y := by
  have hbZ : (i : ℤ)*n1 A+j*n2 A=(ell*normalizedM P.M.base : ℕ)+depth*n0 A := by exact_mod_cast hb
  constructor
  · intro hz
    by_contra hn
    have hd : height < depth := by omega
    have hxi : x+i < ciH A := by omega
    have hyj : y+j < ciG A := by omega
    have he : ((height*n0 A+x*n1 A+y*n2 A+ell*normalizedM P.M.base : ℕ) : ℤ)=
        ((height : ℤ)-depth)*n0 A+(x+i : ℕ)*n1 A+(y+j : ℕ)*n2 A := by
      simp only [Nat.cast_add,Nat.cast_mul] at hbZ ⊢
      nlinarith only [hbZ]
    rw [he] at hz
    have hh := (symmetric_ci_signed_height_mem_iff A hxi hyj ((height : ℤ)-depth)).mp hz
    omega
  · intro hh
    have hd := symmetric_single_return_source_differences A hB hp hi hj hb
    rcases hh with hh | hh | hh
    · have hsub : (height-depth : ℕ)+(depth : ℤ)=height := by exact_mod_cast Nat.sub_add_cancel hh
      have he : ((height*n0 A+x*n1 A+y*n2 A+ell*normalizedM P.M.base : ℕ) : ℤ)=
          ((height-depth)*n0 A+(x+i)*n1 A+(y+j)*n2 A : ℕ) := by
        simp only [Nat.cast_add,Nat.cast_mul] at hbZ ⊢
        nlinarith only [hbZ,hsub]
      rw [he]; exact ci_grid_mem A (height-depth) (x+i) (y+j)
    · have hsub : (x-(ciH A-i) : ℕ)+((ciH A-i : ℕ) : ℤ)=x := by exact_mod_cast Nat.sub_add_cancel hh
      have he : ((height*n0 A+x*n1 A+y*n2 A+ell*normalizedM P.M.base : ℕ) : ℤ)=
          (symmetricX A j depth : ℕ)+
            (height*n0 A+(x-(ciH A-i))*n1 A+y*n2 A : ℕ) := by
        have hd' := hd.2.1
        simp only [Nat.cast_add,Nat.cast_mul] at hd' ⊢
        nlinarith only [hd',hsub]
      rw [he]
      exact int_ideal_add_mem _ (symmetric_single_return_sources_mem A hB hp hi hj hb).2.1.1
        (ci_grid_mem A height (x-(ciH A-i)) y)
    · have hsub : (y-(ciG A-j) : ℕ)+((ciG A-j : ℕ) : ℤ)=y := by exact_mod_cast Nat.sub_add_cancel hh
      have he : ((height*n0 A+x*n1 A+y*n2 A+ell*normalizedM P.M.base : ℕ) : ℤ)=
          (symmetricY A i depth : ℕ)+
            (height*n0 A+x*n1 A+(y-(ciG A-j))*n2 A : ℕ) := by
        have hd' := hd.2.2
        simp only [Nat.cast_add,Nat.cast_mul] at hd' ⊢
        nlinarith only [hd',hsub]
      rw [he]
      exact int_ideal_add_mem _ (symmetric_single_return_sources_mem A hB hp hi hj hb).2.2.1
        (ci_grid_mem A height x (y-(ciG A-j)))

theorem symmetric_routingH_eq_normalizedH (A : SectorBCriticalRoleBranchA P) :
    routingH P.M.base A.reindex = normalizedH P.M.base := by
  have hr : ({n0 A,n1 A,n2 A} : Set ℕ)=Set.range (fun i : Fin 3 => normalizedWeight P.M.base i) := by
    ext z
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨A.reindex 0,rfl⟩
      · exact ⟨A.reindex 1,rfl⟩
      · exact ⟨A.reindex 2,rfl⟩
    · rintro ⟨i,rfl⟩
      obtain ⟨j,rfl⟩ := A.reindex.surjective i
      fin_cases j <;> simp only [n0,n1,n2] <;> simp
  have hn : ({normalizedA P.M.base, normalizedB P.M.base, normalizedC P.M.base} : Set ℕ)=
      Set.range (fun i : Fin 3 => normalizedWeight P.M.base i) := by
    ext z
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp [normalizedA,normalizedB,normalizedC,normalizedWeight,L2B.weights]
  have hset := hr.trans hn.symm
  have hmon : (routingH P.M.base A.reindex).toAddSubmonoid=
      (normalizedH P.M.base).toAddSubmonoid := by
    change generatedThree (routingA P.M.base A.reindex) (routingB P.M.base A.reindex)
      (routingC P.M.base A.reindex)=generatedThree (normalizedA P.M.base)
      (normalizedB P.M.base) (normalizedC P.M.base)
    rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A,generatedThree,generatedThree,hset]
  cases heH : routingH P.M.base A.reindex with
  | mk HH hHH =>
    cases heN : normalizedH P.M.base with
    | mk NN hNN =>
      rw [heH,heN] at hmon
      change HH=NN at hmon
      subst NN
      rfl

/-- Construction for every actual strict-prefix index, not merely a selected
event. All admission conclusions are proved after constructing the Apéry anchor. -/
theorem symmetric_nonprincipal_return_packet (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {ell : ℕ} (hp : 0 < ell)
    (hl : ell < actualPrincipalIndex P.M.base) :
    ∃ i j depth : ℕ, 0 < i ∧ i < ciH A ∧ 0 < j ∧ j < ciG A ∧
      0 < depth ∧ depth < ciK A ∧
      depth < ciU A+((i+ciV A)/ciH A)*ciK A ∧
      i*n1 A+j*n2 A=ell*normalizedM P.M.base+depth*n0 A := by
  let B := P.M.base
  let e := A.reindex
  let HH := routingH B e
  let a := routingA B e
  let n := ell*normalizedM B
  letI : NeZero a := ⟨(routingA_pos B e).ne'⟩
  let beta0 := HH.asRelativeIdeal.aperyRepresentative a (n : ZMod a)
  have hn : n ∉ HH := by
    dsimp only [n,HH,B,e]
    rw [symmetric_routingH_eq_normalizedH A]
    intro hn
    exact (Nat.not_le_of_gt hl) (principalIndex_min _ _ B.q_positive hp hn)
  have hbmem : beta0 ∈ HH.asRelativeIdeal := HH.asRelativeIdeal.aperyRepresentative_mem a _
  have hbmod : (beta0 : ZMod a)=((n : ℤ) : ZMod a) := by
    simpa only [Int.cast_natCast] using HH.asRelativeIdeal.aperyRepresentative_mod a (n : ZMod a)
  have haH : a ∈ HH := by
    dsimp only [a,HH,B,e]
    rw [routingA_eq_n0 A]
    exact nat_mem_of_int_mem (by simpa only [one_mul,zero_mul,add_zero] using ci_grid_mem A 1 0 0)
  have hnlt : (n : ℤ) < beta0 := by
    by_contra hnot
    obtain ⟨k,hk⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq a (by omega) hbmod.symm
    have hm := HH.asRelativeIdeal.add_mem hbmem
      (show a*k ∈ HH from by simpa [nsmul_eq_mul,mul_comm] using HH.toAddSubmonoid.nsmul_mem haH k)
    have hm' : (n : ℤ) ∈ HH.asRelativeIdeal := by
      rw [hk]
      exact hm
    exact hn (nat_mem_of_int_mem hm')
  obtain ⟨depth,hdepth⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq a (le_of_lt hnlt) hbmod
  have hdP : 0 < depth := by
    by_contra hd
    have hd0 : depth=0 := by omega
    simp only [hd0,Nat.cast_zero,mul_zero,add_zero] at hdepth
    omega
  obtain ⟨i,j,hi,hj,hr⟩ := branchA_residue_rectangle_localization A (n : ZMod a)
  have hc := symmetric_ci_rectangle_canonical A hi hj
  change (normalizedGrid B e 0 i j : ℤ)=HH.asRelativeIdeal.aperyRepresentative a (gridResidue B e i j) at hc
  rw [← hr] at hc
  have he : i*n1 A+j*n2 A=n+depth*n0 A := by
    have heZ := hc.trans hdepth
    dsimp only [B,e,a] at heZ
    simp only [normalizedGrid,zero_mul,zero_add,Nat.cast_add,Nat.cast_mul,
      routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A] at heZ
    exact_mod_cast (show (i : ℤ)*n1 A+j*n2 A=(n : ℕ)+(depth : ℤ)*n0 A by nlinarith only [heZ])
  have had := symmetric_single_return_admission A hB hp hi hj he
  exact ⟨i,j,depth,had.1,hi,had.2.1,hj,hdP,had.2.2.1,had.2.2.2,he⟩

private theorem ci_a_axis_not_mem_return (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {ell t : ℕ} (hp : 0 < ell) (ht : t < ciK A) :
    ((t*n0 A : ℕ) : ℤ) ∉ returnIdeal (routingH P.M.base A.reindex) (ell*normalizedM P.M.base) := by
  intro hz
  have hm := symmetric_returnIdeal_le_final A hp hz
  have hd := nat_mem_of_int_mem (ci_grid_mem A (ciK A-1-t) 0 0)
  simp only [zero_mul,add_zero] at hd
  have hs := (routingI P.M.base A.reindex).add_mem hm hd
  have he : ((t*n0 A : ℕ) : ℤ)+((ciK A-1-t)*n0 A : ℕ)=((ciK A-1)*n0 A : ℕ) := by
    have h : t+(ciK A-1-t)=ciK A-1 := by omega
    exact_mod_cast (show t*n0 A+(ciK A-1-t)*n0 A=(ciK A-1)*n0 A by rw [← add_mul,h])
  exact (symmetric_live_pure_predecessors A hB).1 (he ▸ hs)

private theorem prefix_minimal_eq_generator {H : NumericalSemigroup} {m Q : ℕ}
    {s : ℤ} {g : ℕ} (hs : IsSource H (prefixCarrier H m Q) s)
    (hg : (g : ℤ) ∈ prefixCarrier H m Q) (hdiv : s-g ∈ H.asRelativeIdeal) : s=g := by
  obtain ⟨t,ht,he⟩ := hdiv
  by_cases ht0 : t=0
  · simp only [ht0,Nat.cast_zero] at he
    omega
  · exfalso
    apply hs.2 t ht ht0
    have he' : s-(t : ℤ)=(g : ℤ) := by omega
    exact he'.symm ▸ hg

/-- Exact S-SOURCE: no old minimal prefix source is divisible by the principal
source. The proof consumes complementary indices and the actual LIVE fibers. -/
theorem symmetric_principal_does_not_erase_source (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {s : ℤ}
    (hs : IsSource (routingH P.M.base A.reindex)
      (prefixCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base)) s) :
    s-(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) ∉
      (routingH P.M.base A.reindex).asRelativeIdeal := by
  let HH := routingH P.M.base A.reindex
  let m := normalizedM P.M.base
  let Q := actualPrincipalIndex P.M.base
  obtain ⟨ell,hp,hl,hmem⟩ := hs.1
  obtain ⟨i,j,depth,hiP,hi,hjP,hj,hdP,hdK,hdC,hb⟩ := symmetric_nonprincipal_return_packet A hB hp hl
  have hgen := (symmetric_single_return_three_sources A hB hp hi hj hb s).mp hmem
  have hsm := symmetric_single_return_sources_mem A hB hp hi hj hb
  have hfP : (symmetricF A i j : ℤ) ∈ prefixCarrier HH m Q := ⟨ell,hp,hl,hsm.1⟩
  have hxP : (symmetricX A j depth : ℤ) ∈ prefixCarrier HH m Q := ⟨ell,hp,hl,hsm.2.1⟩
  have hyP : (symmetricY A i depth : ℤ) ∈ prefixCarrier HH m Q := ⟨ell,hp,hl,hsm.2.2⟩
  have he : s=(symmetricF A i j : ℕ) ∨ s=(symmetricX A j depth : ℕ) ∨ s=(symmetricY A i depth : ℕ) := by
    rcases hgen with hg | hg | hg
    · exact Or.inl (prefix_minimal_eq_generator hs hfP hg)
    · exact Or.inr (Or.inl (prefix_minimal_eq_generator hs hxP hg))
    · exact Or.inr (Or.inr (prefix_minimal_eq_generator hs hyP hg))
  intro hdiv
  have hkP : 0 < Q-ell := by omega
  have hdiff := symmetric_single_return_source_differences A hB hp hi hj hb
  have hcompl : s-(ell*m : ℕ) ∈ returnIdeal HH ((Q-ell)*m) := by
    constructor
    · rcases he with he | he | he
      · rw [he,hdiff.1]
        simpa only [zero_mul,add_zero] using ci_grid_mem A depth 0 0
      · rw [he,hdiff.2.1]
        simpa only [zero_mul,zero_add,add_zero] using ci_grid_mem A 0 (ciH A-i) 0
      · rw [he,hdiff.2.2]
        simpa only [zero_mul,zero_add] using ci_grid_mem A 0 0 (ciG A-j)
    · change (s-(ell*m : ℕ))-((Q-ell)*m : ℕ) ∈ HH.asRelativeIdeal
      have hqm : ((Q-ell)*m : ℕ)+(ell*m : ℤ)=Q*m := by
        exact_mod_cast (show (Q-ell)*m+ell*m=Q*m by rw [← add_mul,Nat.sub_add_cancel (by omega : ell ≤ Q)])
      have hsame : s-(ell*m : ℕ)-((Q-ell)*m : ℕ)=s-(Q*m : ℕ) := by
        simp only [Nat.cast_mul] at hqm ⊢
        omega
      exact hsame.symm ▸ hdiv
  rcases he with he | he | he
  · rw [he,hdiff.1] at hcompl
    exact ci_a_axis_not_mem_return A hB hkP hdK hcompl
  · rw [he,hdiff.2.1] at hcompl
    exact (ci_axis_not_mem_return A hB hkP).1 (by omega) hcompl
  · rw [he,hdiff.2.2] at hcompl
    exact (ci_axis_not_mem_return A hB hkP).2 (by omega) hcompl

theorem symmetric_principal_source_persistence (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {s : ℤ}
    (hs : IsSource (routingH P.M.base A.reindex)
      (prefixCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base)) s) :
    IsSource (routingH P.M.base A.reindex)
      (finalCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base)) s := by
  refine ⟨Or.inl hs.1, ?_⟩
  intro t ht ht0 hsub
  rcases hsub with hsub | hsub
  · exact hs.2 t ht ht0 hsub
  · apply symmetric_principal_does_not_erase_source A hB hs
    have hm := (routingH P.M.base A.reindex).asRelativeIdeal.add_mem hsub ht
    change s-t-(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)+t ∈
      (routingH P.M.base A.reindex).asRelativeIdeal at hm
    convert hm using 1 <;> ring

abbrev SymmetricReturnIndex (A : SectorBCriticalRoleBranchA P) :=
  {ell : ℕ // 0 < ell ∧ ell < actualPrincipalIndex P.M.base}

private theorem symmetric_return_tuple_exists (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (ell : SymmetricReturnIndex A) :
    ∃ t : ℕ×ℕ×ℕ, 0 < t.1 ∧ t.1 < ciH A ∧ 0 < t.2.1 ∧ t.2.1 < ciG A ∧
      0 < t.2.2 ∧ t.2.2 < ciK A ∧
      t.2.2 < ciU A+((t.1+ciV A)/ciH A)*ciK A ∧
      t.1*n1 A+t.2.1*n2 A=ell.val*normalizedM P.M.base+t.2.2*n0 A := by
  obtain ⟨i,j,d,h⟩ := symmetric_nonprincipal_return_packet A hB ell.property.1 ell.property.2
  exact ⟨(i,j,d),h⟩

def symmetricReturnTuple (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (ell : SymmetricReturnIndex A) : ℕ×ℕ×ℕ :=
  Classical.choose (symmetric_return_tuple_exists A hB ell)

theorem symmetricReturnTuple_spec (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (ell : SymmetricReturnIndex A) :
    let t := symmetricReturnTuple A hB ell
    0 < t.1 ∧ t.1 < ciH A ∧ 0 < t.2.1 ∧ t.2.1 < ciG A ∧
      0 < t.2.2 ∧ t.2.2 < ciK A ∧
      t.2.2 < ciU A+((t.1+ciV A)/ciH A)*ciK A ∧
      t.1*n1 A+t.2.1*n2 A=ell.val*normalizedM P.M.base+t.2.2*n0 A :=
  Classical.choose_spec (symmetric_return_tuple_exists A hB ell)

private theorem nat_min_image_exists {ι : Type*} (hne : Nonempty ι) (f : ι → ℕ) :
    ∃ d : ℕ, ∃ i, f i=d := by
  obtain ⟨i⟩ := hne
  exact ⟨f i,i,rfl⟩

def natMinImage {ι : Type*} (hne : Nonempty ι) (f : ι → ℕ) : ℕ := by
  classical
  exact Nat.find (nat_min_image_exists hne f)

theorem natMinImage_spec {ι : Type*} (hne : Nonempty ι) (f : ι → ℕ) :
    ∃ i, f i=natMinImage hne f := by
  classical
  exact Nat.find_spec (nat_min_image_exists hne f)

theorem natMinImage_le {ι : Type*} (hne : Nonempty ι) (f : ι → ℕ) (i : ι) :
    natMinImage hne f ≤ f i := by
  classical
  exact Nat.find_min' (nat_min_image_exists hne f) ⟨i,rfl⟩

def symmetricReturnNonempty (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Nonempty (SymmetricReturnIndex A) :=
  ⟨⟨1,by omega,hQ⟩⟩

abbrev symmetricDa (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  natMinImage (symmetricReturnNonempty A hQ) (fun ell => (symmetricReturnTuple A hB ell).2.2)
abbrev symmetricDb (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  natMinImage (symmetricReturnNonempty A hQ) (fun ell => ciH A-(symmetricReturnTuple A hB ell).1)
abbrev symmetricDc (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  natMinImage (symmetricReturnNonempty A hQ) (fun ell => ciG A-(symmetricReturnTuple A hB ell).2.1)

theorem symmetric_colon_box_coordinates (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    {x y height : ℕ} (hx : x < ciH A) (hy : y < ciG A) :
    ((height*n0 A+x*n1 A+y*n2 A : ℕ) : ℤ) ∈
      principalColonCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base) ↔
      symmetricDa A hB hQ ≤ height ∨ symmetricDb A hB hQ ≤ x ∨ symmetricDc A hB hQ ≤ y := by
  have hf : actualPrincipalIndex P.M.base*normalizedM P.M.base ∈ routingH P.M.base A.reindex := by
    rw [symmetric_routingH_eq_normalizedH A]
    exact (actualPrincipalIndex_spec P.M.base).2
  rw [principal_colon_cyclic_reverse _ _ _ hf]
  have hmem := ci_grid_mem A height x y
  have hsingle (ell : SymmetricReturnIndex A) :
      ((height*n0 A+x*n1 A+y*n2 A : ℕ) : ℤ)+(ell.val*normalizedM P.M.base : ℕ) ∈
        (routingH P.M.base A.reindex).asRelativeIdeal ↔
        (symmetricReturnTuple A hB ell).2.2 ≤ height ∨
        ciH A-(symmetricReturnTuple A hB ell).1 ≤ x ∨
        ciG A-(symmetricReturnTuple A hB ell).2.1 ≤ y := by
    have S := symmetricReturnTuple_spec A hB ell
    simpa only [Nat.cast_add] using symmetric_single_return_colon_threshold A hB ell.property.1
      S.2.1 S.2.2.2.1 S.2.2.2.2.2.2.2 hx hy
  constructor
  · rintro ⟨_,ell,hp,hl,hm⟩
    let k : SymmetricReturnIndex A := ⟨ell,hp,hl⟩
    rcases (hsingle k).mp hm with hd | hd | hd
    · exact Or.inl ((natMinImage_le _ _ k).trans hd)
    · exact Or.inr (Or.inl ((natMinImage_le _ _ k).trans hd))
    · exact Or.inr (Or.inr ((natMinImage_le _ _ k).trans hd))
  · intro hh
    refine ⟨hmem,?_⟩
    rcases hh with hh | hh | hh
    · obtain ⟨ell,he⟩ := natMinImage_spec (symmetricReturnNonempty A hQ)
        (fun ell => (symmetricReturnTuple A hB ell).2.2)
      exact ⟨ell.val,ell.property.1,ell.property.2,(hsingle ell).mpr (Or.inl (he ▸ hh))⟩
    · obtain ⟨ell,he⟩ := natMinImage_spec (symmetricReturnNonempty A hQ)
        (fun ell => ciH A-(symmetricReturnTuple A hB ell).1)
      exact ⟨ell.val,ell.property.1,ell.property.2,(hsingle ell).mpr (Or.inr (Or.inl (he ▸ hh)))⟩
    · obtain ⟨ell,he⟩ := natMinImage_spec (symmetricReturnNonempty A hQ)
        (fun ell => ciG A-(symmetricReturnTuple A hB ell).2.1)
      exact ⟨ell.val,ell.property.1,ell.property.2,(hsingle ell).mpr (Or.inr (Or.inr (he ▸ hh)))⟩

theorem symmetric_colon_box_ci_relations_vanish (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    0 < symmetricDa A hB hQ ∧ 0 < symmetricDb A hB hQ ∧ 0 < symmetricDc A hB hQ ∧
      symmetricDa A hB hQ ≤ ciK A ∧ symmetricDb A hB hQ ≤ ciH A ∧
      symmetricDc A hB hQ ≤ ciG A ∧
      (symmetricDa A hB hQ ≤ ciU A ∨ symmetricDb A hB hQ ≤ ciV A) := by
  let hne := symmetricReturnNonempty A hQ
  obtain ⟨ka,ha⟩ := natMinImage_spec hne (fun ell => (symmetricReturnTuple A hB ell).2.2)
  obtain ⟨kb,hb⟩ := natMinImage_spec hne (fun ell => ciH A-(symmetricReturnTuple A hB ell).1)
  obtain ⟨kc,hc⟩ := natMinImage_spec hne (fun ell => ciG A-(symmetricReturnTuple A hB ell).2.1)
  have Sa := symmetricReturnTuple_spec A hB ka
  have Sb := symmetricReturnTuple_spec A hB kb
  have Sc := symmetricReturnTuple_spec A hB kc
  have haP : 0 < symmetricDa A hB hQ := by change 0 < natMinImage hne _; rw [← ha]; exact Sa.2.2.2.2.1
  have hbP : 0 < symmetricDb A hB hQ := by change 0 < natMinImage hne _; rw [← hb]; omega
  have hcP : 0 < symmetricDc A hB hQ := by change 0 < natMinImage hne _; rw [← hc]; omega
  refine ⟨haP,hbP,hcP,?_,?_,?_,?_⟩
  · change natMinImage hne _ ≤ ciK A
    rw [← ha]; exact Nat.le_of_lt Sa.2.2.2.2.2.1
  · change natMinImage hne _ ≤ ciH A
    rw [← hb]; exact Nat.sub_le _ _
  · change natMinImage hne _ ≤ ciG A
    rw [← hc]; exact Nat.sub_le _ _
  · by_cases hunwrapped : ∃ ell : SymmetricReturnIndex A, (symmetricReturnTuple A hB ell).1+ciV A < ciH A
    · obtain ⟨ell,he⟩ := hunwrapped
      have S := symmetricReturnTuple_spec A hB ell
      have hcost := S.2.2.2.2.2.2.1
      rw [Nat.div_eq_of_lt he,zero_mul,add_zero] at hcost
      exact Or.inl (le_trans (natMinImage_le hne _ ell) (Nat.le_of_lt hcost))
    · have hi := Sb.2.1
      have hbwrap : ciH A ≤ (symmetricReturnTuple A hB kb).1+ciV A := by
        by_contra hn
        exact hunwrapped ⟨kb,by omega⟩
      right
      change natMinImage hne _ ≤ ciV A
      rw [← hb]
      omega

/-- A canonical tail Apéry point in the prefix is generated by an actual F.
X/Y are excluded by their positive a-coordinate, not by source/target naming. -/
theorem symmetric_canonical_prefix_F_divisor (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {x y : ℕ} (hx : x < ciH A) (hy : y < ciG A)
    (hz : ((x*n1 A+y*n2 A : ℕ) : ℤ) ∈
      prefixCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base)) :
    ∃ ell : SymmetricReturnIndex A,
      ((x*n1 A+y*n2 A : ℕ) : ℤ)-
        symmetricF A (symmetricReturnTuple A hB ell).1
          (symmetricReturnTuple A hB ell).2.1 ∈
        (routingH P.M.base A.reindex).asRelativeIdeal := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  obtain ⟨ell,hp,hl,hz⟩ := hz
  let k : SymmetricReturnIndex A := ⟨ell,hp,hl⟩
  have S := symmetricReturnTuple_spec A hB k
  have he := S.2.2.2.2.2.2.2
  have hc := symmetric_ci_rectangle_canonical A hx hy
  change ((normalizedGrid P.M.base A.reindex 0 x y : ℕ) : ℤ)=
    (routingH P.M.base A.reindex).asRelativeIdeal.aperyRepresentative
      (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex x y) at hc
  have hn : ((x*n1 A+y*n2 A : ℕ) : ℤ)-n0 A ∉
      (routingH P.M.base A.reindex).asRelativeIdeal := by
    have hnot := (routingH P.M.base A.reindex).asRelativeIdeal.aperyRepresentative_sub_modulus_not_mem
      (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex x y)
    rw [← hc] at hnot
    simpa only [normalizedGrid,zero_mul,zero_add,routingB_eq_n1 A,
      routingC_eq_n2 A,routingA_eq_n0 A,Nat.cast_add,Nat.cast_mul] using hnot
  rcases (symmetric_single_return_three_sources A hB hp S.2.1 S.2.2.2.1 he _).mp hz
      with hf | hX | hY
  · exact ⟨k,hf⟩
  · exfalso
    apply hn
    have hd := S.2.2.2.2.2.1
    have hXm : (symmetricX A (symmetricReturnTuple A hB k).2.1
        (symmetricReturnTuple A hB k).2.2 : ℤ)-n0 A ∈
        (routingH P.M.base A.reindex).asRelativeIdeal := by
      have hm := ci_grid_mem A (ciK A-(symmetricReturnTuple A hB k).2.2-1) 0
        (symmetricReturnTuple A hB k).2.1
      have hs : ciK A-(symmetricReturnTuple A hB k).2.2 =
          ciK A-(symmetricReturnTuple A hB k).2.2-1+1 := by omega
      have hsZ := congrArg (fun t : ℕ => (t : ℤ)) hs
      simp only [Nat.cast_add,Nat.cast_one] at hsZ
      simp only [symmetricX,Nat.cast_add,Nat.cast_mul,Nat.cast_zero,zero_mul,zero_add,add_zero] at hm ⊢
      convert hm using 1 <;> nlinarith only [hsZ]
    have hm := int_ideal_add_mem (routingH P.M.base A.reindex).asRelativeIdeal hXm hX
    convert hm using 1 <;> ring
  · exfalso
    apply hn
    have hd := S.2.2.2.2.2.2.1
    have hYm : (symmetricY A (symmetricReturnTuple A hB k).1
        (symmetricReturnTuple A hB k).2.2 : ℤ)-n0 A ∈
        (routingH P.M.base A.reindex).asRelativeIdeal := by
      have hm := ci_grid_mem A
        (ciU A+((symmetricReturnTuple A hB k).1+ciV A)/ciH A*ciK A-
          (symmetricReturnTuple A hB k).2.2-1)
        (((symmetricReturnTuple A hB k).1+ciV A)%ciH A) 0
      have hs : ciU A+((symmetricReturnTuple A hB k).1+ciV A)/ciH A*ciK A-
          (symmetricReturnTuple A hB k).2.2 =
          ciU A+((symmetricReturnTuple A hB k).1+ciV A)/ciH A*ciK A-
          (symmetricReturnTuple A hB k).2.2-1+1 := by omega
      have hsZ := congrArg (fun t : ℕ => (t : ℤ)) hs
      simp only [Nat.cast_add,Nat.cast_one] at hsZ
      simp only [symmetricY,Nat.cast_add,Nat.cast_mul,Nat.cast_zero,zero_mul,add_zero] at hm ⊢
      convert hm using 1 <;> nlinarith only [hsZ]
    have hm := int_ideal_add_mem (routingH P.M.base A.reindex).asRelativeIdeal hYm hY
    convert hm using 1 <;> ring

theorem symmetric_final_source_iff (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (s : ℤ) :
    IsSource (routingH P.M.base A.reindex)
      (finalCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base)) s ↔
    s=(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) ∨
      IsSource (routingH P.M.base A.reindex)
        (prefixCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
          (actualPrincipalIndex P.M.base)) s := by
  constructor
  · intro hs
    by_cases he : s=(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)
    · exact Or.inl he
    · exact Or.inr (branchBirth_isPrefixSource ⟨hs,he⟩)
  · rintro (rfl | hs)
    · have hp := principal_is_new_source (normalizedH P.M.base)
        (normalizedM P.M.base) P.M.base.q_positive
      simpa only [symmetric_routingH_eq_normalizedH A] using hp
    · exact symmetric_principal_source_persistence A hB hs

abbrev symmetricPrefixIdeal (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  principalPrefixIdeal (routingH P.M.base A.reindex) (normalizedM P.M.base)
    (actualPrincipalIndex P.M.base) hQ

def symmetricPrefixRouting (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    CombinatorialCore.ResidueData (ZMod (routingA P.M.base A.reindex)) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  exact ((symmetricPrefixIdeal A hQ).toAperyStepData
    (routingA P.M.base A.reindex) (routingB P.M.base A.reindex)
    (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _)).toResidueData
      ((symmetricPrefixIdeal A hQ).toAperyStepData_isValid
        (routingA P.M.base A.reindex) (routingB P.M.base A.reindex)
        (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _))

abbrev symmetricPrefixSources (A : SectorBCriticalRoleBranchA P) :=
  {s : ℤ // IsSource (routingH P.M.base A.reindex)
    (prefixCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)) s}
abbrev symmetricFinalSources (A : SectorBCriticalRoleBranchA P) :=
  {s : ℤ // IsSource (routingH P.M.base A.reindex)
    (finalCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)) s}

def symmetricSourceInsertionEquiv (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) : symmetricFinalSources A ≃ symmetricPrefixSources A ⊕ Unit where
  toFun s := if he : s.val=(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)
    then Sum.inr () else Sum.inl ⟨s.val,branchBirth_isPrefixSource ⟨s.property,he⟩⟩
  invFun s := match s with
    | Sum.inl s => ⟨s.val,symmetric_principal_source_persistence A hB s.property⟩
    | Sum.inr _ => ⟨(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ),
        (symmetric_final_source_iff A hB _).mpr (Or.inl rfl)⟩
  left_inv := by
    intro s
    dsimp only
    by_cases he : s.val=(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)
    · simp only [dif_pos he]
      apply Subtype.ext
      exact he.symm
    · simp only [dif_neg he]
  right_inv := by
    intro s
    cases s with
    | inl s =>
        have hn : s.val ≠ (actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) := by
          intro he
          have hf := principal_not_mem_prefix (normalizedH P.M.base)
            (normalizedM P.M.base) P.M.base.q_positive
          apply hf
          simpa only [symmetric_routingH_eq_normalizedH A,he] using s.property.1
        simp only [dif_neg hn]
    | inr s => cases s; simp

theorem symmetric_source_count_insertion (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Nat.card (symmetricFinalSources A)=Nat.card (symmetricPrefixSources A)+1 := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  let I := symmetricPrefixIdeal A hQ
  have hgen := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base A.reindex)).1
  have inj : Function.Injective (fun s : symmetricPrefixSources A =>
      (s.val : ZMod (routingA P.M.base A.reindex))) := by
    intro s t he
    change (s.val : ZMod (routingA P.M.base A.reindex))=
      (t.val : ZMod (routingA P.M.base A.reindex)) at he
    apply Subtype.ext
    have hs := I.aperyRepresentative_eq_of_isMinimalGenerator
      (routingA P.M.base A.reindex) (routingB P.M.base A.reindex)
      (routingC P.M.base A.reindex) hgen s.property
    have ht := I.aperyRepresentative_eq_of_isMinimalGenerator
      (routingA P.M.base A.reindex) (routingB P.M.base A.reindex)
      (routingC P.M.base A.reindex) hgen t.property
    rw [he] at hs
    exact hs.symm.trans ht
  letI : Finite (symmetricPrefixSources A) := Finite.of_injective _ inj
  simpa only [Nat.card_sum,Nat.card_unique (α := Unit)] using
    Nat.card_congr (symmetricSourceInsertionEquiv A hB)

end NS25Lean.L5A2BFinalRepair
