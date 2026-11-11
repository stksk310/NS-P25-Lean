import NS25Lean.P2CriticalNormalForm

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalShortFibers
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen
  ReturnSourceRigidity ReturnPresentationAdapter PureInternalTransverse CriticalNormalForm

/-- Avoiding every displayed toric side, combined with a genuine full
presentation, proves numerical fiber uniqueness rather than chart uniqueness. -/
theorem unique_of_no_toric_side {H : NumericalSemigroup} (T : Triple H)
    (S : Set (Exponent×Exponent))
    (hgen : Presentation.relationIdeal ℚ S=
      Presentation.relationIdeal ℚ {lr : Exponent×Exponent | T.weight lr.1=T.weight lr.2})
    (M : Exponent) (hshort : ∀ lr∈S, ¬lr.1≤M ∧ ¬lr.2≤M) :
    ∀ z, T.weight z=T.weight M → z=M := by
  apply fiber_unique_of_no_move T (symmetricRelations S)
    (move_connected_of_relationIdeal_eq T S hgen) M
  rintro z ⟨l,r,hlr,d,he,_⟩
  have hl : l≤M := by
    intro i
    have hi := congrArg (fun v : Exponent => v i) he
    simp only [Finsupp.add_apply] at hi
    omega
  rcases hlr with h | h
  · exact (hshort (l,r) h).1 hl
  · exact (hshort (r,l) h).2 hl

theorem short_cut_normal_source_divisor {H : NumericalSemigroup} (T : Triple H)
    (m C u v : ℕ) (htie : C*T.g 1=u*T.g 0+v*T.g 2)
    (S : Set (Exponent×Exponent))
    (hgen : Presentation.relationIdeal ℚ S=
      Presentation.relationIdeal ℚ {lr : Exponent×Exponent | T.weight lr.1=T.weight lr.2})
    (M : Exponent) (hshort : ∀ lr∈S, ¬lr.1≤M ∧ ¬lr.2≤M)
    (hK : T.weight M∈cyclicCut H m) :
    ∃ s : IdealSources H (cyclicCut H m), sourceNormal T m C u v s≤M := by
  obtain ⟨s,g,hg,hle,huniq⟩ := unique_cut_literal_source_divisor H (cyclicCut H m)
    (fun _ h => h.1) T.weight T.factor M hK (unique_of_no_toric_side T S hgen M hshort)
  have he := huniq (sourceNormal T m C u v s) (sourceNormal_degree T m C u v htie s)
  exact ⟨s,he ▸ hle⟩

theorem cut_normal_source_divisor_of_unique {H : NumericalSemigroup} (T : Triple H)
    (m C u v : ℕ) (htie : C*T.g 1=u*T.g 0+v*T.g 2)
    (M : Exponent) (hUF : ∀ z, T.weight z=T.weight M → z=M)
    (hK : T.weight M∈cyclicCut H m) :
    ∃ s : IdealSources H (cyclicCut H m), sourceNormal T m C u v s≤M := by
  obtain ⟨s,g,hg,hle,huniq⟩ := unique_cut_literal_source_divisor H (cyclicCut H m)
    (fun _ h => h.1) T.weight T.factor M hK hUF
  have he := huniq (sourceNormal T m C u v s) (sourceNormal_degree T m C u v htie s)
  exact ⟨s,he ▸ hle⟩

/-- True outside exponents give the axis version without a chosen toric
presentation or any assumption that a chart degree has a unique normal. -/
theorem subcritical_axis_source_divisor {H : NumericalSemigroup} (T : Triple H)
    (D : Critical T) (m C u v : ℕ) (htie : C*T.g 1=u*T.g 0+v*T.g 2)
    (i : Fin 3) (n : ℕ) (hn : n<D.exponent i)
    (hK : n*T.g i∈cyclicCut H m) :
    ∃ s : IdealSources H (cyclicCut H m), sourceNormal T m C u v s≤Finsupp.single i n := by
  apply cut_normal_source_divisor_of_unique T m C u v htie (Finsupp.single i n)
  · intro z hz
    rw [T.weight_single] at hz
    exact D.subcritical_unique i hn z hz
  · simpa only [T.weight_single] using hK

end NS25Lean.CriticalShortFibers
