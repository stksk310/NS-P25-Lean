import NS25Lean.P2SectorCM5MinimalGeneratorsR33
import NS25Lean.P2SectorCT6GlobalLedgerR24

set_option linter.style.header false
set_option linter.style.whitespace false
noncomputable section
namespace NS25Lean.L5A2C4OR34
open L5A1 L5A2C4A L5A2C4OR19 L5A2C4OR20 L5A2C4OR22 L5A2C4OR23
  L5A2C4OR29 L5A2C4OR32 L5A2C4OR33
variable {Gamma : NumericalSemigroup}

/-- Literal frozen socle predicate depends only on the monomial closure. -/
theorem monomialSocle_closure_congr {G H : Set Monomial}
    (h : monomialClosure G = monomialClosure H) (z : Monomial) :
    MonomialSocle G z ↔ MonomialSocle H z := by
  unfold MonomialSocle
  rw [h]

theorem polynomialMinimal_closure_congr {G H : Set Monomial}
    (h : monomialClosure G = monomialClosure H) (z : Monomial) :
    PolynomialMinimal G z ↔ PolynomialMinimal H z := by
  unfold PolynomialMinimal
  rw [h]

def predicateSubtypeEquiv {A : Type*} {p q : A → Prop} (h : ∀ a, p a ↔ q a) :
    {a // p a} ≃ {a // q a} where
  toFun a := ⟨a.val,(h a.val).mp a.property⟩
  invFun a := ⟨a.val,(h a.val).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sourceWrap_y_zero {P : P2Data Gamma} (R : ActualRolePacket P) (z : Monomial) :
    (sourceWrap R z).2.1 = 0 := rfl

theorem sourceWrap_not_fullySupported {P : P2Data Gamma}
    (R : ActualRolePacket P) (z : Monomial) : ¬ FullySupported (sourceWrap R z) := by
  simp [FullySupported,sourceWrap]

theorem boundary_not_fullySupported {P : P2Data Gamma} (R : ActualRolePacket P) :
    ¬ FullySupported (boundaryAliveMonomial R) := by
  classical
  unfold boundaryAliveMonomial
  split_ifs <;> simp [FullySupported]

theorem fullySupported_survivingWrap_false {P : P2Data Gamma} (R : ActualRolePacket P)
    {g : Monomial} (hg : g ∈ survivingSourceWraps R) : ¬ FullySupported g := by
  obtain ⟨s,_,rfl⟩ := hg.1
  exact sourceWrap_not_fullySupported R _

/-- Exhaustive full-support classification in the WHOLE initial ideal. -/
theorem full_minimal_iff_source_normal {P : P2Data Gamma} (R : ActualRolePacket P)
    (g : Monomial) :
    PolynomialMinimal (initialGenerators R) g ∧ FullySupported g ↔
      ∃ s : ModelSources P.M.base R.e, sourceNormal R s = g ∧
        FullySupported (sourceNormal R s) := by
  constructor
  · rintro ⟨hm,hf⟩
    have hi := minimal_mem_initial R ((polynomialMinimal_iff R g).mp hm)
    rw [initial_eq_raw_union_wraps] at hi
    rcases hi with hr | ⟨s,_,rfl⟩
    · rcases hr with (rfl | ⟨s,rfl⟩) | rfl
      · exact (by simpa [FullySupported] using hf : False).elim
      · exact ⟨s,rfl,hf⟩
      · exact (boundary_not_fullySupported R hf).elim
    · exact (sourceWrap_not_fullySupported R _ hf).elim
  · rintro ⟨s,rfl,hf⟩
    exact ⟨(polynomialMinimal_iff R _).mpr
      (raw_is_minimal R (Or.inl (Or.inr ⟨s,rfl⟩))),hf⟩

/-- Source labels and fully-supported minimal exponent seats agree exactly. -/
def fullySupported_minima_equiv_sources {P : P2Data Gamma} (R : ActualRolePacket P) :
    {g // PolynomialMinimal (initialGenerators R) g ∧ FullySupported g} ≃
      {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} := by
  let f : {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} →
      {g // PolynomialMinimal (initialGenerators R) g ∧ FullySupported g} :=
    fun s => ⟨sourceNormal R s.val,
      (full_minimal_iff_source_normal R _).mpr ⟨s.val,rfl,s.property⟩⟩
  apply (Equiv.ofBijective f ?_).symm
  constructor
  · intro s t h
    apply Subtype.ext
    exact sourceNormal_injective R (congrArg Subtype.val h)
  · intro g
    obtain ⟨s,hs,hf⟩ := (full_minimal_iff_source_normal R g.val).mp g.property
    exact ⟨⟨s,hf⟩,Subtype.ext hs⟩

theorem fullySupported_minima_card {P : P2Data Gamma} (R : ActualRolePacket P) :
    Nat.card {g // PolynomialMinimal (initialGenerators R) g ∧ FullySupported g} =
      Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} :=
  Nat.card_congr (fullySupported_minima_equiv_sources R)

theorem initialMinimalFinset_socle_card_eq {P : P2Data Gamma} (R : ActualRolePacket P) :
    Nat.card {z // MonomialSocle (initialMinimalFinset R : Set Monomial) z} =
      Nat.card {z // MonomialSocle (initialGenerators R) z} :=
  Nat.card_congr (predicateSubtypeEquiv
    (monomialSocle_closure_congr (initialMinimalFinset_closure R)))

theorem initialMinimalFinset_polynomialMinimal_iff {P : P2Data Gamma}
    (R : ActualRolePacket P) (g : Monomial) :
    PolynomialMinimal (initialMinimalFinset R : Set Monomial) g ↔
      g ∈ initialMinimalFinset R := by
  rw [polynomialMinimal_closure_congr (initialMinimalFinset_closure R),
    polynomialMinimal_iff,mem_initialMinimalFinset]

theorem initialMinimalFinset_minimal_card {P : P2Data Gamma} (R : ActualRolePacket P) :
    Nat.card {g // PolynomialMinimal (initialMinimalFinset R : Set Monomial) g} =
      P.sourceCount+2+survivingWrapCount R := by
  have he : {g // PolynomialMinimal (initialMinimalFinset R : Set Monomial) g} ≃
      initialMinimalFinset R :=
    predicateSubtypeEquiv (initialMinimalFinset_polynomialMinimal_iff R)
  rw [Nat.card_congr he,Nat.card_eq_finsetCard]
  exact initialMinimalFinset_card R

theorem initialMinimalFinset_full_card_eq {P : P2Data Gamma} (R : ActualRolePacket P) :
    Nat.card {g // PolynomialMinimal (initialMinimalFinset R : Set Monomial) g ∧
      FullySupported g} =
      Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} := by
  have he : {g // PolynomialMinimal (initialMinimalFinset R : Set Monomial) g ∧
      FullySupported g} ≃
      {g // PolynomialMinimal (initialGenerators R) g ∧ FullySupported g} :=
    predicateSubtypeEquiv (fun g => and_congr_left (fun _ =>
    polynomialMinimal_closure_congr (initialMinimalFinset_closure R) g))
  exact (Nat.card_congr he).trans (fullySupported_minima_card R)

/-- Original M6 binder, with no branch, cap, B=0, or support restriction. -/
theorem actual_initial_socle_source_bound :
    ∀ {Gamma : NumericalSemigroup} {P : P2Data Gamma} (R : ActualRolePacket P),
      Nat.card {z // MonomialSocle (initialGenerators R) z}+2 ≤
        P.sourceCount+2+survivingWrapCount R+
        Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} := by
  intro Gamma P R
  have hp : (0,0,0) ∉ monomialClosure (initialMinimalFinset R : Set Monomial) := by
    rw [initialMinimalFinset_closure]
    exact initial_proper R
  have ha := initial_axes R
  rw [←initialMinimalFinset_closure R] at ha
  have hb := L5A2C4OR24.abstract_monomial_socle_bound_general (initialMinimalFinset R) hp ha
  rwa [initialMinimalFinset_socle_card_eq,initialMinimalFinset_minimal_card,
    initialMinimalFinset_full_card_eq] at hb

end NS25Lean.L5A2C4OR34
