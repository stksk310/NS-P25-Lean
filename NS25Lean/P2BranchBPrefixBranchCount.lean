import NS25Lean.P2BranchBPrefixInverseAxis

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}
local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

def NonsymmetricPrefixFSources (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  {s : ℤ // (nonsymmetricPrefixIdeal R hQ).IsMinimalGenerator s ∧
    ∃ ell : NonsymmetricReturnIndex R, s=(nonsymmetricF R
      (nonsymmetricReturnTuple R hB ell).1 (nonsymmetricReturnTuple R hB ell).2.1 : ℕ)}

def NonsymmetricPrefixCenterSlot (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :=
  {u : Unit // ∃ ell : NonsymmetricReturnIndex R,
    (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
    (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R}

private theorem source_minimal (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) {r : ZMod (nsA R)}
    (hs : (nonsymmetricPrefixRouting R hQ).IsSource r) :
    (nonsymmetricPrefixIdeal R hQ).IsMinimalGenerator (nonsymmetricPrefixLambda R hQ r) := by
  have hgen := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base (nsReindex R))).1
  have pos := nonsymmetric_generators_positive R
  exact ((nonsymmetricPrefixIdeal R hQ).concrete_isSource_iff_isMinimalGenerator
    (nsA R) (nsB R) (nsC R) hgen (routingHB _ _) (routingHC _ _) pos.2.1.ne' pos.2.2.ne' r).mp hs

theorem nonsymmetric_prefix_F_sources_finite (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Finite (NonsymmetricPrefixFSources R hB hQ) := by
  let f : NonsymmetricPrefixFSources R hB hQ → ZMod (nsA R) := fun s => (s.val : ZMod (nsA R))
  apply Finite.of_injective f
  intro s t he
  apply Subtype.ext
  have hgen := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base (nsReindex R))).1
  have hs := (nonsymmetricPrefixIdeal R hQ).aperyRepresentative_eq_of_isMinimalGenerator
    (nsA R) (nsB R) (nsC R) hgen s.property.1
  have ht := (nonsymmetricPrefixIdeal R hQ).aperyRepresentative_eq_of_isMinimalGenerator
    (nsA R) (nsB R) (nsC R) hgen t.property.1
  change (s.val : ZMod (nsA R))=(t.val : ZMod (nsA R)) at he
  rw [he] at hs
  exact hs.symm.trans ht

private def hasF (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (s : L5A2C4I.ResidueData.CSourceTargetBranches (nonsymmetricPrefixRouting R hQ)) : Prop :=
  ∃ ell : NonsymmetricReturnIndex R,
    nonsymmetricPrefixLambda R hQ ((nonsymmetricPrefixRouting R hQ).branchTarget s.val)=
      (nonsymmetricF R (nonsymmetricReturnTuple R hB ell).1 (nonsymmetricReturnTuple R hB ell).2.1 : ℕ)

def nonsymmetricPrefixBranchResource (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (s : L5A2C4I.ResidueData.CSourceTargetBranches (nonsymmetricPrefixRouting R hQ)) :
    NonsymmetricPrefixFSources R hB hQ ⊕ NonsymmetricPrefixCenterSlot R hB :=
  if hf : hasF R hB hQ s then
    Sum.inl ⟨nonsymmetricPrefixLambda R hQ ((nonsymmetricPrefixRouting R hQ).branchTarget s.val),
      source_minimal R hQ s.property.2,hf⟩
  else
    Sum.inr ⟨(),((nonsymmetric_prefix_C_targets_F_or_origin R hB hQ s.property.1 s.property.2).resolve_left hf).2⟩

theorem nonsymmetricPrefixBranchResource_injective (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricPrefixBranchResource R hB hQ) := by
  intro s t he
  apply Subtype.ext
  apply (nonsymmetricPrefixRouting R hQ).branchTarget_injective
  by_cases hs : hasF R hB hQ s <;> by_cases ht : hasF R hB hQ t
  · simp only [nonsymmetricPrefixBranchResource,dif_pos hs,dif_pos ht,Sum.inl.injEq] at he
    have hv := congrArg Subtype.val (Sum.inl.inj he)
    have hm := congrArg (fun z : ℤ => (z : ZMod (nsA R))) hv
    simpa only [nonsymmetricPrefixLambda,RelativeIdeal.aperyRepresentative_mod] using hm
  · simp only [nonsymmetricPrefixBranchResource,dif_pos hs,dif_neg ht,Sum.inl_ne_inr] at he
    cases he
  · simp only [nonsymmetricPrefixBranchResource,dif_neg hs,dif_pos ht,Sum.inr_ne_inl] at he
    cases he
  · have hso := ((nonsymmetric_prefix_C_targets_F_or_origin R hB hQ s.property.1 s.property.2).resolve_left hs).1
    have hto := ((nonsymmetric_prefix_C_targets_F_or_origin R hB hQ t.property.1 t.property.2).resolve_left ht).1
    exact hso.trans hto.symm

theorem nonsymmetric_prefix_C_count_bound (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Nat.card (L5A2C4I.ResidueData.CSourceTargetBranches (nonsymmetricPrefixRouting R hQ)) ≤
      Nat.card (NonsymmetricPrefixFSources R hB hQ)+Nat.card (NonsymmetricPrefixCenterSlot R hB) := by
  letI := nonsymmetric_prefix_F_sources_finite R hB hQ
  letI : Finite (NonsymmetricPrefixCenterSlot R hB) := Subtype.finite
  have he := Nat.card_le_card_of_injective _ (nonsymmetricPrefixBranchResource_injective R hB hQ)
  simpa only [Nat.card_sum] using he

theorem nonsymmetric_prefix_center_slot_count (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :
    Nat.card (NonsymmetricPrefixCenterSlot R hB)=
      if (∃ ell : NonsymmetricReturnIndex R,
        (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
        (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) then 1 else 0 := by
  unfold NonsymmetricPrefixCenterSlot
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  split_ifs with h
  · simp only [h,Finset.filter_true,Nat.card_eq_fintype_card,Finset.card_univ,Fintype.card_unit]
  · simp only [h,Finset.filter_false,Finset.card_empty]

end NS25Lean.L5A2BFinalRepair
