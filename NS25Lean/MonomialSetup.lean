import NS25Lean.FourBasePreparation
import Mathlib.Data.Finsupp.PWO
import Mathlib.RingTheory.Jacobson.Artinian

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3A
open MvPolynomial

abbrev Exponent := Fin 3 →₀ ℕ
abbrev Polynomial (k : Type*) [CommSemiring k] := MvPolynomial (Fin 3) k
variable {k : Type*} [Field k]

/-- Divisibility-minimal monomials actually belonging to the ideal. -/
def minimalExponents (I : Ideal (Polynomial k)) : Set Exponent :=
  {a | Minimal (fun b => monomial b (1 : k) ∈ I) a}

def FullSupport (a : Exponent) : Prop := ∀ i, 0 < a i

def fullSupportGenerators (I : Ideal (Polynomial k)) : Set Exponent :=
  {a | a ∈ minimalExponents I ∧ FullSupport a}

def q_fs (I : Ideal (Polynomial k)) : ℕ := (fullSupportGenerators I).ncard

/-- The minimum over arbitrary polynomial ideal generating families. -/
def mu (I : Ideal (Polynomial k)) : ℕ := I.spanFinrank

theorem minimalExponents_finite (I : Ideal (Polynomial k)) :
    (minimalExponents I).Finite :=
  (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (Set.isPWO_of_wellQuasiOrderedLE _)

instance (I : Ideal (Polynomial k)) : Finite (minimalExponents I) :=
  (minimalExponents_finite I).to_subtype

theorem fullSupportGenerators_finite (I : Ideal (Polynomial k)) :
    (fullSupportGenerators I).Finite :=
  (minimalExponents_finite I).subset (fun _ h => h.1)

theorem monomial_mem_span_iff (S : Set Exponent) (a : Exponent) :
    monomial a (1 : k) ∈ Ideal.span ((fun b => monomial b (1 : k)) '' S) ↔
      ∃ b ∈ S, b ≤ a := by
  classical
  simp [mem_ideal_span_monomial_image]

theorem exists_minimal_le (I : Ideal (Polynomial k)) (a : Exponent)
    (ha : monomial a (1 : k) ∈ I) : ∃ b ≤ a, b ∈ minimalExponents I :=
  (Set.isPWO_of_wellQuasiOrderedLE {b | monomial b (1 : k) ∈ I}).exists_le_minimal ha

theorem minimalExponents_generate (I : Ideal (Polynomial k))
    (hI : L2B.IsMonomialIdeal k I) :
    Ideal.span ((fun a => monomial a (1 : k)) '' minimalExponents I) = I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact ha.1
  · obtain ⟨S, hS⟩ := hI
    nth_rw 1 [hS]
    apply Ideal.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    have haI : monomial a (1 : k) ∈ I := hS ▸ Ideal.subset_span ⟨a, ha, rfl⟩
    obtain ⟨b, hba, hb⟩ := exists_minimal_le I a haI
    exact (monomial_mem_span_iff _ _).mpr ⟨b, hb, hba⟩

def minimalMonomial (I : Ideal (Polynomial k)) (a : minimalExponents I) : Polynomial k :=
  monomial a.val 1

theorem minimalMonomial_range (I : Ideal (Polynomial k)) :
    Set.range (minimalMonomial I) =
      (fun a => monomial a (1 : k)) '' minimalExponents I := by
  ext f
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a.val, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩

theorem minimalMonomial_irredundant (I : Ideal (Polynomial k)) (a : minimalExponents I) :
    minimalMonomial I a ∉ Ideal.span (minimalMonomial I '' {b | b ≠ a}) := by
  classical
  intro h
  have he : minimalMonomial I '' {b | b ≠ a} =
      (fun u => monomial u (1 : k)) '' (Subtype.val '' {b : minimalExponents I | b ≠ a}) :=
    by
      change (fun b : minimalExponents I => monomial b.val (1 : k)) '' {b | b ≠ a} = _
      exact (Set.image_image (fun u => monomial u (1 : k))
        (fun b : minimalExponents I => b.val) {b | b ≠ a}).symm
  rw [he] at h
  obtain ⟨b, ⟨c, hca, rfl⟩, hle⟩ := (monomial_mem_span_iff _ a.val).mp h
  exact hca (Subtype.ext (le_antisymm hle (a.property.2 c.property.1 hle)))

/-- Monomial minimality agrees with the minimum number of arbitrary ideal generators. -/
theorem mu_eq_minimal_count (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I) :
    mu I = (minimalExponents I).ncard := by
  classical
  letI := Fintype.ofFinite (minimalExponents I)
  have hgen : Ideal.span (Set.range (minimalMonomial I)) = I := by
    rw [minimalMonomial_range, minimalExponents_generate I hI]
  apply le_antisymm
  · change I.spanFinrank ≤ _
    nth_rw 1 [← hgen]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans
      (by
        rw [← Set.image_univ]
        exact (Set.ncard_image_le (Set.toFinite _)).trans_eq (by simp))
  · obtain ⟨s, hcard, hs⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (show I.FG from Ideal.fg_of_isNoetherianRing I)
    have hb := PositivePresentation.homogeneous_card_le_generators
      (fun _ : Fin 3 => 1) (fun _ => Nat.zero_lt_one) (minimalMonomial I)
      (fun a => Finsupp.weight (fun _ : Fin 3 => 1) a.val)
      (fun a => isWeightedHomogeneous_monomial _ _ _ rfl)
      (minimalMonomial_irredundant I) s (hs.trans hgen.symm)
    simpa only [mu, ← hcard, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hb

/-- Actual annihilator of the three variables in the quotient. -/
def socle (I : Ideal (Polynomial k)) : Submodule k (Polynomial k ⧸ I) where
  carrier := {x | ∀ i, Ideal.Quotient.mk I (X i) * x = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb i; rw [mul_add, ha i, hb i, add_zero]
  smul_mem' := by intro c a ha i; rw [mul_smul_comm, ha i, smul_zero]

def quotientType (I : Ideal (Polynomial k)) : ℕ := Module.finrank k (socle I)

theorem mem_socle_iff (I : Ideal (Polynomial k)) (x : Polynomial k ⧸ I) :
    x ∈ socle I ↔ ∀ i, Ideal.Quotient.mk I (X i) * x = 0 := Iff.rfl

theorem quotient_finite_of_artinian (I : Ideal (Polynomial k))
    [IsArtinianRing (Polynomial k ⧸ I)] : Module.Finite k (Polynomial k ⧸ I) :=
  Module.finite_of_isArtinianRing k (Polynomial k ⧸ I)

theorem socle_finite_of_artinian (I : Ideal (Polynomial k))
    [IsArtinianRing (Polynomial k ⧸ I)] : Module.Finite k (socle I) := by
  letI := quotient_finite_of_artinian I
  infer_instance

/-- The general paper setting, without any type inequality in its fields. -/
structure ArtinianMonomial (k : Type*) [Field k] where
  ideal : Ideal (Polynomial k)
  monomial : L2B.IsMonomialIdeal k ideal
  proper : ideal ≠ ⊤
  artinian : IsArtinianRing (Polynomial k ⧸ ideal)

end NS25Lean.L3A
