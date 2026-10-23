import NS25Lean.MonomialStaircase

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3A
open MvPolynomial
variable {k : Type*} [Field k]

/-- Actual mixed divisibility-minimal generators in the Y,Z plane. -/
def MixedCorners (I : Ideal (Polynomial k)) :=
  {g : minimalExponents I // g.val 0 = 0 ∧ 0 < g.val 1 ∧ 0 < g.val 2}

instance (I : Ideal (Polynomial k)) : Finite (MixedCorners I) :=
  Subtype.finite

theorem monomial_mem_of_le (I : Ideal (Polynomial k))
    (hI : L2B.IsMonomialIdeal k I) {a b : Exponent}
    (ha : monomial a (1 : k) ∈ I) (hab : a ≤ b) : monomial b (1 : k) ∈ I := by
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨g, hg, hga⟩ := (monomial_mem_span_iff S a).mp ha
  exact (monomial_mem_span_iff S b).mpr ⟨g, hg, hga.trans hab⟩

theorem standard_of_le (I : Ideal (Polynomial k))
    (hI : L2B.IsMonomialIdeal k I) {a b : Exponent}
    (hb : b ∈ standardExponents I) (hab : a ≤ b) : a ∈ standardExponents I := by
  intro ha
  exact hb (monomial_mem_of_le I hI ha hab)

theorem standard_below_minimal (I : Ideal (Polynomial k))
    (g : minimalExponents I) (a : Exponent) (hle : a ≤ g.val) (hne : a ≠ g.val) :
    a ∈ standardExponents I := by
  intro ha
  exact hne ((show Minimal (fun b => monomial b (1 : k) ∈ I) g.val from
    g.property).eq_of_le ha hle)

private theorem socle_Y_injective (I : Ideal (Polynomial k))
    (hI : L2B.IsMonomialIdeal k I)
    (hX : ∀ a ∈ standardExponents I, a 0 = 0) :
    Function.Injective (fun a : socleExponents I => a.val 1) := by
  intro a b he
  have h0a := hX a.val a.property.1
  have h0b := hX b.val b.property.1
  have hz : a.val 2 = b.val 2 := by
    apply le_antisymm
    · by_contra hn
      have hle : b.val + Finsupp.single 2 1 ≤ a.val := by
        intro i
        fin_cases i <;> simp only [Finsupp.add_apply, Finsupp.single_apply] <;> simp_all
      exact a.property.1 (monomial_mem_of_le I hI (b.property.2 2) hle)
    · by_contra hn
      have hle : a.val + Finsupp.single 2 1 ≤ b.val := by
        intro i
        fin_cases i <;> simp only [Finsupp.add_apply, Finsupp.single_apply] <;> simp_all
      exact b.property.1 (monomial_mem_of_le I hI (a.property.2 2) hle)
  apply Subtype.ext
  ext i
  fin_cases i <;> simp_all

private def nextCorner (I : Ideal (Polynomial k)) (a : socleExponents I) :
    minimalExponents I :=
  ⟨(exists_minimal_le I (a.val + Finsupp.single 1 1) (a.property.2 1)).choose,
    (exists_minimal_le I (a.val + Finsupp.single 1 1) (a.property.2 1)).choose_spec.2⟩

private theorem nextCorner_le (I : Ideal (Polynomial k)) (a : socleExponents I) :
    (nextCorner I a).val ≤ a.val + Finsupp.single 1 1 :=
  (exists_minimal_le I (a.val + Finsupp.single 1 1) (a.property.2 1)).choose_spec.1

private theorem nextCorner_coordinates (I : Ideal (Polynomial k))
    (hI : L2B.IsMonomialIdeal k I)
    (hX : ∀ a ∈ standardExponents I, a 0 = 0) (a : socleExponents I) :
    (nextCorner I a).val 0 = 0 ∧ (nextCorner I a).val 1 = a.val 1 + 1 := by
  have hle := nextCorner_le I a
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  simp only [Finsupp.add_apply, Finsupp.single_apply] at h0 h1 h2
  simp only [Fin.reduceEq, ite_false, ite_true, add_zero] at h0 h1 h2
  have hx := hX a.val a.property.1
  have hzero : (nextCorner I a).val 0 = 0 := by omega
  refine ⟨hzero, ?_⟩
  by_contra hn
  have hga : (nextCorner I a).val ≤ a.val := by
    intro i
    fin_cases i <;> simp_all <;> omega
  exact a.property.1 (monomial_mem_of_le I hI (nextCorner I a).property.1 hga)

private theorem pureY_minimal_unique (I : Ideal (Polynomial k))
    (a b : minimalExponents I)
    (ha0 : a.val 0 = 0) (hb0 : b.val 0 = 0)
    (ha2 : a.val 2 = 0) (hb2 : b.val 2 = 0) : a = b := by
  apply Subtype.ext
  rcases le_total (a.val 1) (b.val 1) with h | h
  · exact (show Minimal (fun g => monomial g (1 : k) ∈ I) b.val from b.property).eq_of_le
      a.property.1 (by intro i; fin_cases i <;> simp_all)
  · exact (show Minimal (fun g => monomial g (1 : k) ∈ I) a.val from a.property).eq_of_ge
      b.property.1 (by intro i; fin_cases i <;> simp_all)

private def socleCornerCode (I : Ideal (Polynomial k))
    (hI : L2B.IsMonomialIdeal k I)
    (hX : ∀ a ∈ standardExponents I, a 0 = 0) (a : socleExponents I) :
    Option (MixedCorners I) := by
  classical
  exact if hz : (nextCorner I a).val 2 = 0 then none else
    some ⟨nextCorner I a, (nextCorner_coordinates I hI hX a).1,
      by rw [(nextCorner_coordinates I hI hX a).2]; omega, Nat.pos_of_ne_zero hz⟩

private theorem socleCornerCode_injective (I : Ideal (Polynomial k))
    (hI : L2B.IsMonomialIdeal k I)
    (hX : ∀ a ∈ standardExponents I, a 0 = 0) :
    Function.Injective (socleCornerCode I hI hX) := by
  classical
  intro a b he
  apply socle_Y_injective I hI hX
  have hga := nextCorner_coordinates I hI hX a
  have hgb := nextCorner_coordinates I hI hX b
  have hg : nextCorner I a = nextCorner I b := by
    by_cases ha : (nextCorner I a).val 2 = 0
    · by_cases hb : (nextCorner I b).val 2 = 0
      · exact pureY_minimal_unique I _ _ hga.1 hgb.1 ha hb
      · simp [socleCornerCode, ha, hb] at he
    · by_cases hb : (nextCorner I b).val 2 = 0
      · simp [socleCornerCode, ha, hb] at he
      · have hs := Option.some.inj (by
          simpa only [socleCornerCode, dite_eq_right ha, dite_eq_right hb] using he)
        exact congrArg Subtype.val hs
  have hy := congrArg (fun g : minimalExponents I => g.val 1) hg
  change a.val 1 = b.val 1
  omega

/-- One pure-Y end plus the actual mixed corners bounds the maximal
standard monomials. No corner-count conclusion is part of the input. -/
theorem socle_card_le_mixed_corners_add_one (I : Ideal (Polynomial k))
    (hI : L2B.IsMonomialIdeal k I)
    (hX : ∀ a ∈ standardExponents I, a 0 = 0) :
    Nat.card (socleExponents I) ≤ Nat.card (MixedCorners I) + 1 := by
  classical
  letI := Fintype.ofFinite (MixedCorners I)
  have h := Nat.card_le_card_of_injective (socleCornerCode I hI hX)
    (socleCornerCode_injective I hI hX)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option] using h

end NS25Lean.L3A
