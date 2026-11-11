import NS25Lean.PrincipalTensorColonPresentationLayers
import NS25Lean.PrincipalTensorColonExact
import NS25Lean.P2ReturnExchange

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace NS25Lean.PrincipalTensorColon
open L5A2BFinalRepair L3A MvPolynomial ToricPresentation
open PrincipalTensorColonLayers PrincipalTensorColonExact
variable {k : Type*} [Field k] {H : NumericalSemigroup}
  {I : RelativeIdeal H} {f : H.toAddSubmonoid} {g : Fin 3 → H.toAddSubmonoid}
variable (T : GradedPresentation (k:=k) I f g)

abbrev CutQuotient (T : GradedPresentation (k:=k) I f g) :=
  SemigroupAlgebra k H.toAddSubmonoid ⧸
    (carrierMonomialIdeal k I ⊔ Ideal.span {AddMonoidAlgebra.single f (1:k)})

def cutGenerator (T : GradedPresentation (k:=k) I f g) (i : Fin 3) : CutQuotient T :=
  Ideal.Quotient.mkₐ k _ (AddMonoidAlgebra.single (g i) 1)

/-- The actual short exact sequence 0→T(-f)→R/I→R/(I,t^f)→0,
constructed from the graded colon equivalence. -/
def principalSequence : ExactData (k:=k) (Poly T) (Carrier (k:=k) I) (CutQuotient T) where
  c := generators T
  a := carrierGenerators (k:=k) I g
  b := cutGenerator T
  i := inject T
  p := principalFinalProjection (k:=k) (carrierMonomialIdeal k I) (AddMonoidAlgebra.single f 1)
  injective := inject_injective T
  surjective := principalFinalProjection_surjective _ _
  exact := by
    rw [← principalFinalProjection_exact]
    ext z
    constructor
    · rintro ⟨w,rfl⟩
      exact ⟨T.equiv w,rfl⟩
    · rintro ⟨w,rfl⟩
      exact ⟨T.equiv.symm w,by simp [inject]⟩
  compat_i := inject_generator T
  compat_p := by
    intro i z
    change (Ideal.Quotient.factorₐ k (show carrierMonomialIdeal k I ≤
      carrierMonomialIdeal k I ⊔ Ideal.span {AddMonoidAlgebra.single f (1:k)} from le_sup_left))
        (carrierGenerators (k:=k) I g i*z)=_
    rw [map_mul]
    rfl

theorem principal_connecting_comparison_zero (z : FinalH0 (principalSequence T)) :
    comparisonH1 T (connecting (principalSequence T) z)=0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (fun i => inject T (connectingPre (principalSequence T) z i))∈
    LinearMap.range (threeKoszulD0 (k:=k) (carrierGenerators (k:=k) I g))
  refine ⟨linearLift (principalSequence T) z.val,?_⟩
  ext i
  exact (connectingPre_image (principalSequence T) z i).symm

/-- Shared principal-cut estimate for an arbitrary numerically graded tensor
colon. The rank estimate is derived from the actual staircase mixed cycles.
In particular neither its rank nor the final type inequality is an input. -/
theorem principal_tensor_cut_socle_gain_le_two (hf : (f.val:ℤ)∉I) :
    Module.finrank k (LinearMap.ker (threeKoszulD0 (k:=k) (cutGenerator T))) ≤
      Module.finrank k (CarrierH0 (k:=k) I g)+2 := by
  letI := carrierMonomialQuotient_finite (k:=k) I
  letI := tensor_poly_finite T
  letI := tensor_bivariate_finite T
  letI := Module.Finite.of_surjective
    (principalFinalProjection (k:=k) (carrierMonomialIdeal k I) (AddMonoidAlgebra.single f 1))
    (principalFinalProjection_surjective _ _)
  obtain ⟨e,he⟩ := tensor_poly_operator_packet T
  have hh1 := cohomology_finrank_of_operators T.D T.positive (generators T)
    (tensorBivariateGenerator T 0) (tensorBivariateGenerator T 1) e he
  have hh2 := plane_H2_finrank T.J T.monomialJ (tensor_bivariate_proper T hf) T.plane
  change Module.finrank k (TwoKoszulH2 (k:=k) (tensorBivariateGenerator T 0)
    (tensorBivariateGenerator T 1))=1 at hh2
  rw [hh2] at hh1
  have hh0 := h0_finrank_of_operators T.D T.positive (generators T)
    (tensorBivariateGenerator T 0) (tensorBivariateGenerator T 1) e he
  have hj0 := plane_H0_eq_socle T.J T.plane
  change TwoKoszulH0 (k:=k) (tensorBivariateGenerator T 0) (tensorBivariateGenerator T 1)=L3A.socle T.J at hj0
  rw [hj0,Module.finrank_eq_nat_card_basis (L3A.socleBasis T.J T.monomialJ)] at hh0
  have hcount := socle_card_le_mixed_corners_add_one T.J T.monomialJ T.plane
  have hrank := mixed_corner_count_le_comparison_rank T
  have hnegative := principal_finrank_balance_le
    (h0Injection (principalSequence T)) (h0Projection (principalSequence T))
    (connecting (principalSequence T)) (comparisonH1 T)
    (h0Injection_injective (principalSequence T))
    (h0Projection_exact (principalSequence T)) (connecting_exact (principalSequence T)) (by
      rintro _ ⟨z,rfl⟩
      exact principal_connecting_comparison_zero T z)
  have hker : ColonH0 (principalSequence T)=LinearMap.ker (threeKoszulD0 (k:=k) (generators T)) := by
    ext z
    change (∀ i, generators T i*z=0) ↔ (fun i => generators T i*z)=0
    simp only [funext_iff,Pi.zero_apply]
  rw [hker] at hnegative
  change Module.finrank k (LinearMap.ker (threeKoszulD0 (k:=k) (cutGenerator T)))+
    Module.finrank k (LinearMap.ker (threeKoszulD0 (k:=k) (generators T)))+
    Module.finrank k (LinearMap.range (comparisonH1 T)) ≤
    Module.finrank k (CarrierH0 (k:=k) I g)+Module.finrank k (ThreeKoszulH1 (k:=k) (generators T)) at hnegative
  change Nat.card (MixedCorners T.J)≤_ at hrank
  omega

/-- Source insertion 1-e combines with Δtype≤2 with the sign 1+e. -/
theorem principal_tensor_cut_source_corrected
    (hf : (f.val:ℤ)∉I) (oldSources newSources erased : ℕ)
    (hsources : newSources+erased=oldSources+1) :
    (Module.finrank k (LinearMap.ker (threeKoszulD0 (k:=k) (cutGenerator T))):ℤ)-newSources ≤
      (Module.finrank k (CarrierH0 (k:=k) I g):ℤ)-oldSources+1+erased := by
  have ht := principal_tensor_cut_socle_gain_le_two T hf
  omega

/-- Natural carrier of the actual monomial ideal, used for literal sources. -/
def naturalCarrier (I : RelativeIdeal H) : Set ℕ := {n | n∈H ∧ (n:ℤ)∈I}

theorem naturalCarrier_add (I : RelativeIdeal H) :
    ∀ x∈naturalCarrier I, ∀ d∈H, x+d∈naturalCarrier I := by
  intro x hx d hd
  refine ⟨H.add_mem hx.1 hd,?_⟩
  simpa only [RelativeIdeal.mem_carrier,Nat.cast_add] using I.add_mem hx.2 hd

theorem naturalCarrier_sources_finite (I : RelativeIdeal H) :
    Finite (ReturnExchange.IdealSources H (naturalCarrier I)) := by
  obtain ⟨c,hc⟩ := H.exists_conductor
  obtain ⟨N,hN⟩ := I.exists_tail
  apply ReturnExchange.ideal_sources_finite_of_tail H (naturalCarrier I) (max c N.toNat)
  intro n hn
  refine ⟨hc n (by omega),hN (n:ℤ) (by omega)⟩

/-- Fully attached source correction. The insertion identity is proved by the
literal source equivalence; no source-count equality is a hypothesis. -/
theorem principal_tensor_cut_type_minus_sources (hf : (f.val:ℤ)∉I) :
    (Module.finrank k (LinearMap.ker (threeKoszulD0 (k:=k) (cutGenerator T))):ℤ)-
      Nat.card (ReturnExchange.IdealSources H (ReturnExchange.principalAdjoin H (naturalCarrier I) f.val)) ≤
    (Module.finrank k (CarrierH0 (k:=k) I g):ℤ)-
      Nat.card (ReturnExchange.IdealSources H (naturalCarrier I))+1+
      Nat.card {s : ReturnExchange.IdealSources H (naturalCarrier I) // ReturnExchange.PrincipalErased H f.val s} := by
  letI := naturalCarrier_sources_finite I
  have hfn : f.val∉naturalCarrier I := fun h => hf h.2
  exact principal_tensor_cut_source_corrected T hf _ _ _
    (ReturnExchange.principal_adjoin_source_count H (naturalCarrier I) (naturalCarrier_add I) f.val hfn)

#print axioms principal_tensor_cut_socle_gain_le_two
#print axioms principal_tensor_cut_source_corrected
#print axioms principal_tensor_cut_type_minus_sources
end NS25Lean.PrincipalTensorColon
