import NS25Lean.InactiveBinomialFibers
import NS25Lean.P2ReturnSourceRigidity

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.ReturnPresentationAdapter
open ReturnSourceRigidity ErasedSourceScreen

def symmetricRelations (S : Set (Exponent×Exponent)) : Set (Exponent×Exponent) :=
  {p | p∈S ∨ (p.2,p.1)∈S}

theorem contextStep_iff_move (S : Set (Exponent×Exponent)) (e f : Exponent) :
    L3C.ContextStep S e f ↔ Move (symmetricRelations S) e f := by
  constructor
  · rintro ⟨⟨l,r⟩,hlr,d,h⟩
    rcases h with ⟨he,hf⟩ | ⟨he,hf⟩
    · exact ⟨l,r,Or.inl hlr,d,by simpa only [add_comm] using he,
        by simpa only [add_comm] using hf⟩
    · exact ⟨r,l,Or.inr hlr,d,by simpa only [add_comm] using he,
        by simpa only [add_comm] using hf⟩
  · rintro ⟨l,r,hlr,d,he,hf⟩
    rcases hlr with hlr | hlr
    · exact ⟨(l,r),hlr,d,Or.inl ⟨by simpa only [add_comm] using he,
        by simpa only [add_comm] using hf⟩⟩
    · exact ⟨(r,l),hlr,d,Or.inr ⟨by simpa only [add_comm] using he,
        by simpa only [add_comm] using hf⟩⟩

theorem contextPath_move (S : Set (Exponent×Exponent)) {e f : Exponent}
    (hp : L3C.ContextPath S e f) :
    Relation.ReflTransGen (Move (symmetricRelations S)) e f := by
  induction hp with
  | refl => exact .refl
  | tail _ hs ih => exact .tail ih ((contextStep_iff_move S _ _).mp hs)

/-- A genuine equality of binomial ideals supplies full contextual fiber
connectivity over the same numerical weight, with no B/P2Data parameter. -/
theorem connected_of_relationIdeal_eq {H : NumericalSemigroup} (T : Triple H)
    (S : Set (Exponent×Exponent))
    (hgen : Presentation.relationIdeal ℚ S=
      Presentation.relationIdeal ℚ {lr : Exponent×Exponent | T.weight lr.1=T.weight lr.2})
    (e f : Exponent) (he : T.weight e=T.weight f) :
    L3C.ContextPath S e f := by
  have hmem : Presentation.relationBinomial ℚ (e,f)∈Presentation.relationIdeal ℚ S := by
    rw [hgen]
    exact Ideal.subset_span ⟨(e,f),he,rfl⟩
  exact L3C.generated_contextPath S e f (Presentation.generated_of_relationBinomial_mem ℚ S e f hmem)

theorem move_connected_of_relationIdeal_eq {H : NumericalSemigroup} (T : Triple H)
    (S : Set (Exponent×Exponent))
    (hgen : Presentation.relationIdeal ℚ S=
      Presentation.relationIdeal ℚ {lr : Exponent×Exponent | T.weight lr.1=T.weight lr.2}) :
    ∀ e f : Exponent, T.weight e=T.weight f →
      Relation.ReflTransGen (Move (symmetricRelations S)) e f := by
  intro e f he
  exact contextPath_move S (connected_of_relationIdeal_eq T S hgen e f he)

end NS25Lean.ReturnPresentationAdapter
