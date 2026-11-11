import NS25Lean.PrincipalTensorColon

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.PrincipalTensorColon
open L5A2BFinalRepair L3A MvPolynomial ToricPresentation FourGeneratedBridge
variable {k : Type*} [Field k] {H : NumericalSemigroup}

/-- The same integer relative ideal after adjoining the actual principal
monomial. Only its intersection with H contributes to the carrier algebra. -/
def principalAdjoinedIdeal (I : RelativeIdeal H) (f : H.toAddSubmonoid) : RelativeIdeal H where
  carrier := {z | z∈I ∨ ∃ d∈H, z=(f.val:ℤ)+(d:ℤ)}
  nonempty := by
    obtain ⟨z,hz⟩ := I.nonempty
    exact ⟨z,Or.inl hz⟩
  bddBelow := by
    obtain ⟨b,hb⟩ := I.bddBelow
    refine ⟨min b (f.val:ℤ),?_⟩
    intro z hz
    rcases hz with hz | ⟨d,hd,rfl⟩
    · exact le_trans (min_le_left _ _) (hb hz)
    · have hb : min b (f.val:ℤ)≤(f.val:ℤ) := min_le_right _ _
      omega
  add_mem := by
    intro z h hz hh
    rcases hz with hz | ⟨d,hd,he⟩
    · exact Or.inl (I.add_mem hz hh)
    · exact Or.inr ⟨d+h,H.add_mem hd hh,by push_cast; omega⟩

@[simp] theorem principalAdjoinedIdeal_mem (I : RelativeIdeal H) (f : H.toAddSubmonoid) (z : ℤ) :
    z∈principalAdjoinedIdeal I f ↔ z∈I ∨ ∃ d∈H, z=(f.val:ℤ)+(d:ℤ) := Iff.rfl

/-- The final literal relative ideal and the actual algebraic principal cut
have exactly the same monomial ideal. -/
theorem principalAdjoinedIdeal_monomial_eq (I : RelativeIdeal H) (f : H.toAddSubmonoid) :
    carrierMonomialIdeal k (principalAdjoinedIdeal I f)=
      carrierMonomialIdeal k I ⊔ Ideal.span {AddMonoidAlgebra.single f (1:k)} := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨h,hh,rfl⟩
    rcases (principalAdjoinedIdeal_mem I f _).mp hh with hp | ⟨d,hd,he⟩
    · exact (show carrierMonomialIdeal k I≤_ from le_sup_left) (Ideal.subset_span ⟨h,hp,rfl⟩)
    · let dH : H.toAddSubmonoid := ⟨d,hd⟩
      have eh : h=f+dH := by apply Subtype.ext; change h.val=f.val+d; omega
      apply (show Ideal.span {AddMonoidAlgebra.single f (1:k)}≤_ from le_sup_right)
      apply Ideal.mem_span_singleton.mpr
      refine ⟨AddMonoidAlgebra.single dH 1,?_⟩
      rw [AddMonoidAlgebra.of'_apply,AddMonoidAlgebra.single_mul_single,one_mul,←eh]
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨h,hh,rfl⟩
      exact Ideal.subset_span ⟨h,Or.inl hh,rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      apply Ideal.subset_span
      exact ⟨f,Or.inr ⟨0,H.zero_mem,by simp⟩,AddMonoidAlgebra.of'_apply _⟩

/-- Natural carrier equality fixes the H, integer ideal, and principal degree
used by both the algebraic surgery and literal source insertion. -/
theorem naturalCarrier_principalAdjoinedIdeal (I : RelativeIdeal H) (f : H.toAddSubmonoid) :
    naturalCarrier (principalAdjoinedIdeal I f)=ReturnExchange.principalAdjoin H (naturalCarrier I) f.val := by
  ext n
  constructor
  · rintro ⟨hn,hin⟩
    rcases hin with hin | ⟨d,hd,he⟩
    · exact Or.inl ⟨hn,hin⟩
    · exact Or.inr ⟨d,hd,by omega⟩
  · rintro (hn | ⟨d,hd,rfl⟩)
    · exact ⟨hn.1,Or.inl hn.2⟩
    · exact ⟨H.add_mem f.property hd,Or.inr ⟨d,hd,by simp⟩⟩

variable {I : RelativeIdeal H} {f : H.toAddSubmonoid} {g : Fin 3 → H.toAddSubmonoid}
variable (T : GradedPresentation (k:=k) I f g)

/-- Exact endpoint dictionary, derived from genuine positive triple generation. -/
theorem cutH0_finrank_integralSocle_card
    (hgen : H.IsGeneratedByThree (g 0).val (g 1).val (g 2).val)
    (hpos : ∀ i, 0<(g i).val) :
    Module.finrank k (LinearMap.ker (threeKoszulD0 (k:=k) (cutGenerator T)))=
      Nat.card {w // IsIntegralSocle (principalAdjoinedIdeal I f) w} := by
  let e := Ideal.quotientEquivAlgOfEq k (principalAdjoinedIdeal_monomial_eq (k:=k) I f).symm
  let e3 := LinearEquiv.piCongrRight (fun _ : Fin 3 => e.toLinearEquiv)
  have hc : ∀ t, threeKoszulD0 (k:=k) (carrierGenerators (k:=k) (principalAdjoinedIdeal I f) g) (e t)=
      e3 (threeKoszulD0 (k:=k) (cutGenerator T) t) := by
    intro t
    ext i
    change carrierGenerators (k:=k) (principalAdjoinedIdeal I f) g i*e t=e (cutGenerator T i*t)
    rw [map_mul]
    congr 1
  have heq := (MixedLayers.kernelEquiv (threeKoszulD0 (k:=k) (cutGenerator T))
    (threeKoszulD0 (k:=k) (carrierGenerators (k:=k) (principalAdjoinedIdeal I f) g))
    e.toLinearEquiv e3 hc).finrank_eq
  exact heq.trans (carrierH0_finrank_integralSocle_card (k:=k) (principalAdjoinedIdeal I f) g
    hgen (fun i => (hpos i).ne'))

/-- Literal integral-socle version of the shared graded tensor principal cut. -/
theorem principal_tensor_cut_integralSocle_card_le_two
    (T : GradedPresentation (k:=k) I f g)
    (hf : (f.val:ℤ)∉I)
    (hgen : H.IsGeneratedByThree (g 0).val (g 1).val (g 2).val)
    (hpos : ∀ i, 0<(g i).val) :
    Nat.card {w // IsIntegralSocle (principalAdjoinedIdeal I f) w} ≤
      Nat.card {w // IsIntegralSocle I w}+2 := by
  have ht := principal_tensor_cut_socle_gain_le_two T hf
  rwa [cutH0_finrank_integralSocle_card T hgen hpos,
    carrierH0_finrank_integralSocle_card (k:=k) I g hgen (fun i => (hpos i).ne')] at ht

/-- Literal integral-socle/source correction for the same two integer ideals.
The erasure count is the actual old minimal-source subtype divisible by f. -/
theorem principal_tensor_cut_integralSocle_minus_sources
    (T : GradedPresentation (k:=k) I f g)
    (hf : (f.val:ℤ)∉I)
    (hgen : H.IsGeneratedByThree (g 0).val (g 1).val (g 2).val)
    (hpos : ∀ i, 0<(g i).val) :
    (Nat.card {w // IsIntegralSocle (principalAdjoinedIdeal I f) w}:ℤ)-
      Nat.card (ReturnExchange.IdealSources H (naturalCarrier (principalAdjoinedIdeal I f))) ≤
    (Nat.card {w // IsIntegralSocle I w}:ℤ)-
      Nat.card (ReturnExchange.IdealSources H (naturalCarrier I))+1+
      Nat.card {s : ReturnExchange.IdealSources H (naturalCarrier I) // ReturnExchange.PrincipalErased H f.val s} := by
  have ht := principal_tensor_cut_type_minus_sources T hf
  rwa [cutH0_finrank_integralSocle_card T hgen hpos,
    carrierH0_finrank_integralSocle_card (k:=k) I g hgen (fun i => (hpos i).ne'),
    ←naturalCarrier_principalAdjoinedIdeal I f] at ht

#check principal_tensor_cut_integralSocle_card_le_two
#check principal_tensor_cut_integralSocle_minus_sources
#print axioms principal_tensor_cut_integralSocle_card_le_two
#print axioms principal_tensor_cut_integralSocle_minus_sources
end NS25Lean.PrincipalTensorColon
