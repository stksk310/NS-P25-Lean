import NS25Lean.P2BranchBActualExceptionalIncidence

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B2A2 L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2C4H CombinatorialCore

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

private theorem routingB_ne_zero (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingB B e ≠ 0 := by
  intro hz
  apply (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).2.2.1
  simpa only [routingB, hz] using (AddSubmonoid.zero_mem _)

private theorem routingC_ne_zero (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingC B e ≠ 0 := by
  intro hz
  apply (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).2.2.2
  simpa only [routingC, hz] using (AddSubmonoid.zero_mem _)

private theorem numericalSemigroup_ext {H K : NumericalSemigroup}
    (h : ∀ n : ℕ, n ∈ H ↔ n ∈ K) : H = K := by
  cases H with
  | mk H hH =>
    cases K with
    | mk K hK =>
      have hsub : H = K := AddSubmonoid.ext h
      subst K
      rfl

/-- Reindexing only permutes the three normalized tail generators. -/
theorem branchBRoutingH_eq_normalizedH
    (R : SectorBCriticalRoleBranchB P) :
    routingH P.M.base (branchBInactiveReindex R) = normalizedH P.M.base := by
  let e := branchBInactiveReindex R
  apply numericalSemigroup_ext
  intro n
  change n ∈ generatedThree (routingA P.M.base e) (routingB P.M.base e)
      (routingC P.M.base e) ↔
    n ∈ generatedThree (L5A2B4AR1.normalizedA P.M.base)
      (L5A2B4AR1.normalizedB P.M.base) (L5A2B4AR1.normalizedC P.M.base)
  have hd := routingD_eq_chosenTailGcd P.M.base e
  let d := tailGcd (P.M.base.tailDegrees 0).val
    (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val
  have hrange :
      Set.range (fun i : Fin 3 => (P.M.base.tailDegrees (e i)).val / d) =
        Set.range (fun i : Fin 3 => (P.M.base.tailDegrees i).val / d) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  have hroute :
      ({routingA P.M.base e, routingB P.M.base e, routingC P.M.base e} : Set ℕ) =
        Set.range (fun i : Fin 3 => (P.M.base.tailDegrees (e i)).val / d) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (hz | hz | hz)
      · exact ⟨0, by simpa [routingA, routingN1, tailValue, d, hd] using hz.symm⟩
      · exact ⟨1, by simpa [routingB, routingN2, tailValue, d, hd] using hz.symm⟩
      · exact ⟨2, by simpa [routingC, routingN3, tailValue, d, hd] using hz.symm⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl (by simp [routingA, routingN1, tailValue, d, hd])
      · exact Or.inr (Or.inl (by simp [routingB, routingN2, tailValue, d, hd]))
      · exact Or.inr (Or.inr (by simp [routingC, routingN3, tailValue, d, hd]))
  have hcanonical :
      ({L5A2B4AR1.normalizedA P.M.base, L5A2B4AR1.normalizedB P.M.base,
          L5A2B4AR1.normalizedC P.M.base} : Set ℕ) =
        Set.range (fun i : Fin 3 => (P.M.base.tailDegrees i).val / d) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (hz | hz | hz)
      · exact ⟨0, by simpa [L5A2B4AR1.normalizedA, d] using hz.symm⟩
      · exact ⟨1, by simpa [L5A2B4AR1.normalizedB, d] using hz.symm⟩
      · exact ⟨2, by simpa [L5A2B4AR1.normalizedC, d] using hz.symm⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl (by simp [L5A2B4AR1.normalizedA, d])
      · exact Or.inr (Or.inl (by simp [L5A2B4AR1.normalizedB, d]))
      · exact Or.inr (Or.inr (by simp [L5A2B4AR1.normalizedC, d]))
  have hset :
      ({routingA P.M.base e, routingB P.M.base e, routingC P.M.base e} : Set ℕ) =
        {L5A2B4AR1.normalizedA P.M.base, L5A2B4AR1.normalizedB P.M.base,
          L5A2B4AR1.normalizedC P.M.base} :=
    hroute.trans (hrange.trans hcanonical.symm)
  simpa [generatedThree, hset]

/-- The actual nonprincipal exceptional source makes the otherwise possibly
empty prefix carrier into an honest relative ideal. -/
noncomputable def branchBActualPrefixIdeal
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val) :
    RelativeIdeal (routingH P.M.base (branchBInactiveReindex R)) where
  carrier := prefixCarrier (routingH P.M.base (branchBInactiveReindex R)) (normalizedM P.M.base)
    (actualPrincipalIndex P.M.base)
  nonempty :=
    ⟨(branchBActualExceptionalNormalizedSource P R x).val,
      (by simpa [branchBRoutingH_eq_normalizedH R] using
        (branchBirth_isPrefixSource hsx).1)⟩
  bddBelow := by
    obtain ⟨u, hu⟩ :=
      (routingH P.M.base (branchBInactiveReindex R)).asRelativeIdeal.bddBelow
    refine ⟨u, ?_⟩
    intro z hz
    obtain ⟨ell, hellpos, helllt, hzJ⟩ := hz
    exact hu hzJ.1
  add_mem := by
    intro z h hz hh
    obtain ⟨ell, hellpos, helllt, hzJ⟩ := hz
    exact ⟨ell, hellpos, helllt, (returnIdeal _ _).add_mem hzJ hh⟩

/-- Guard 1: prefix membership is obtained from the actual BranchBirth
witness, not from the word "nonprincipal" alone. -/
theorem branchB_actualExceptional_mem_prefixCarrier
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val) :
    (branchBActualExceptionalNormalizedSource P R x).val ∈
      prefixCarrier (normalizedH P.M.base) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base) :=
  (branchBirth_isPrefixSource hsx).1

/-- Prefix routing uses the same inactive residue chart and the same `b,c`
translations as final routing, but its Apéry data comes from `K^-`. -/
noncomputable def branchBActualPrefixRoutingData
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    ResidueData (ZMod (routingA P.M.base e)) := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let I := branchBActualPrefixIdeal R x hsx
  exact ((I.toAperyStepData (routingA P.M.base e) (routingB P.M.base e)
      (routingC P.M.base e) (routingHB P.M.base e) (routingHC P.M.base e)).toResidueData
    (I.toAperyStepData_isValid (routingA P.M.base e) (routingB P.M.base e)
      (routingC P.M.base e) (routingHB P.M.base e) (routingHC P.M.base e)))

/-- The actual source is the prefix Apéry representative at the very same
inactive-chart residue `r_x`; in particular it is an actual prefix routing
source. -/
theorem branchB_actualExceptional_prefix_source_packet
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Iminus := branchBActualPrefixIdeal R x hsx
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let r := branchBActualExceptionalRoutingSource P R x
    let s := branchBActualExceptionalNormalizedSource P R x
    Gminus.IsSource r.val ∧
      Iminus.aperyRepresentative (routingA P.M.base e) r.val = s.val ∧
      (s.val : ZMod (routingA P.M.base e)) = r.val := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Iminus := branchBActualPrefixIdeal R x hsx
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let r := branchBActualExceptionalRoutingSource P R x
  let s := branchBActualExceptionalNormalizedSource P R x
  have hprefix : IsSource (routingH P.M.base e)
      (prefixCarrier (routingH P.M.base e) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base)) s.val := by
    dsimp [e]
    rw [branchBRoutingH_eq_normalizedH R]
    exact branchBirth_isPrefixSource hsx
  have hmin : Iminus.IsMinimalGenerator s.val := by
    exact hprefix
  have hrep0 : Iminus.aperyRepresentative (routingA P.M.base e)
      (s.val : ZMod (routingA P.M.base e)) = s.val :=
    Iminus.aperyRepresentative_eq_of_isMinimalGenerator
      (routingA P.M.base e) (routingB P.M.base e) (routingC P.M.base e)
      (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base e)).1 hmin
  have hfinal := branchB_actualExceptional_source_packet P R x
  have hres : (s.val : ZMod (routingA P.M.base e)) = r.val := by
    calc
      (s.val : ZMod (routingA P.M.base e)) =
          ((routingI P.M.base e).aperyRepresentative
            (routingA P.M.base e) r.val : ZMod (routingA P.M.base e)) := by
              rw [hfinal.2.2.2.1]
      _ = r.val := (routingI P.M.base e).aperyRepresentative_mod
        (routingA P.M.base e) r.val
  have hrep : Iminus.aperyRepresentative (routingA P.M.base e) r.val = s.val := by
    rw [← hres]
    exact hrep0
  have hsource : Gminus.IsSource r.val := by
    apply (Iminus.concrete_isSource_iff_isMinimalGenerator
      (routingA P.M.base e) (routingB P.M.base e) (routingC P.M.base e)
      (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base e)).1
      (routingHB P.M.base e) (routingHC P.M.base e)
      (routingB_ne_zero P.M.base e) (routingC_ne_zero P.M.base e) r.val).2
    simpa [hrep] using hmin
  exact ⟨hsource, hrep, hres⟩

/-- Exact prefix branch semantics.  The edge-nonzero form is derived from
this theorem rather than baked into the birth predicate. -/
theorem branchBActualPrefixRouting_isBranch_iff
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (A : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Gminus := branchBActualPrefixRoutingData R x hsx
    Gminus.IsBranch A ↔ Gminus.u A = 0 ∧ Gminus.v A = 0 := by
  rfl

/-- OLD means that the same base `A` was already a branch in prefix routing,
with the same actual source residue as target in both charts. -/
def IsOldActualBranch
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val) : Prop :=
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let G := routingData P.M.base e
  let Iminus := branchBActualPrefixIdeal R x hsx
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let s := branchBActualExceptionalNormalizedSource P R x
  Gminus.IsSource r.val ∧
    Iminus.aperyRepresentative (routingA P.M.base e) r.val = s.val ∧
    (s.val : ZMod (routingA P.M.base e)) = r.val ∧ Gminus.IsBranch A ∧
    Gminus.branchTarget A = r.val ∧ G.IsBranch A ∧ G.branchTarget A = r.val

/-- A genuine zero-edge birth is the complementary same-base event: the
final chart has the actual branch while prefix routing does not. -/
def IsActualZeroEdgeBirth
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val) : Prop :=
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let G := routingData P.M.base e
  let Iminus := branchBActualPrefixIdeal R x hsx
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let s := branchBActualExceptionalNormalizedSource P R x
  Gminus.IsSource r.val ∧
    Iminus.aperyRepresentative (routingA P.M.base e) r.val = s.val ∧
    (s.val : ZMod (routingA P.M.base e)) = r.val ∧ ¬ Gminus.IsBranch A ∧
    Gminus.branchTarget A = r.val ∧ G.IsBranch A ∧ G.branchTarget A = r.val

/-- Non-branch prefix semantics gives the promised zero-edge disjunction. -/
theorem branchB_actualZeroEdgeBirth_edge_nonzero
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let A := x.val.val.val
    Gminus.u A ≠ 0 ∨ Gminus.v A ≠ 0 := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A := x.val.val.val
  have hnot : ¬ Gminus.IsBranch A := hbirth.2.2.2.1
  by_cases hu : Gminus.u A = 0
  · right
    intro hv
    exact hnot ((branchBActualPrefixRouting_isBranch_iff R x hsx A).2 ⟨hu, hv⟩)
  · exact Or.inl hu

/-- B28 SILVER: every nonprincipal actual exceptional branch is, at its own
base and its own target residue, either OLD or an actual zero-edge birth. -/
theorem branchB_actualExceptional_nonprincipal_principalSurgery_channel
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val) :
    IsOldActualBranch R x hsx ∨ IsActualZeroEdgeBirth R x hsx := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let G := routingData P.M.base e
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  have hprefix := branchB_actualExceptional_prefix_source_packet R x hsx
  have hfinal := branchB_actualExceptional_final_branch_incidence P R x
  have htarget : Gminus.branchTarget A = r.val := by
    change G.branchTarget A = r.val
    exact hfinal.2
  by_cases hold : Gminus.IsBranch A
  · left
    exact ⟨hprefix.1, hprefix.2.1, hprefix.2.2, hold,
      htarget, hfinal.1, hfinal.2⟩
  · right
    exact ⟨hprefix.1, hprefix.2.1, hprefix.2.2, hold,
      htarget, hfinal.1, hfinal.2⟩

/-- TARGET is retained as a separate principal disjunct; only the genuine
nonprincipal channel is refined into OLD versus zero-edge birth. -/
theorem branchB_actualExceptional_principal_or_principalSurgery_channel
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) :
    let s := branchBActualExceptionalNormalizedSource P R x
    s.val = (actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) ∨
      ∃ hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
          (actualPrincipalIndex P.M.base) s.val,
        IsOldActualBranch R x hsx ∨ IsActualZeroEdgeBirth R x hsx := by
  let s := branchBActualExceptionalNormalizedSource P R x
  rcases branchB_actualExceptional_source_principal_or_birth P R x with
      htarget | hsx
  · exact Or.inl htarget
  · exact Or.inr ⟨hsx,
      branchB_actualExceptional_nonprincipal_principalSurgery_channel R x hsx⟩

end NS25Lean.L5A2B4AR5B
