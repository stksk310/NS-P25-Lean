import NS25Lean.ToricPresentation
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.GroupTheory.Congruence.Hom

set_option linter.style.header false

/-!
# Congruence relations and their binomial ideals

The relation object is combinatorial. Membership of a monic binomial in its
relation ideal detects exactly the generated additive congruence. In particular,
Noetherianity proves finite presentability of every congruence on a finite free
commutative additive monoid. No generator-number invariant is identified by definition.
-/

noncomputable section
namespace NS25Lean.Presentation

variable (k : Type*) [Field k]
variable {M : Type*} [AddCommMonoid M]

def generatedCongruence (r : Set (M × M)) : AddCon M :=
  addConGen (fun x y => (x, y) ∈ r)

def relationBinomial (p : M × M) : AddMonoidAlgebra k M :=
  AddMonoidAlgebra.single p.1 1 - AddMonoidAlgebra.single p.2 1

def relationIdeal (r : Set (M × M)) : Ideal (AddMonoidAlgebra k M) :=
  Ideal.span (relationBinomial k '' r)

theorem relationBinomial_mem_of_generated (r : Set (M × M)) (x y : M)
    (h : generatedCongruence r x y) : relationBinomial k (x, y) ∈ relationIdeal k r := by
  induction h with
  | of x y h => exact Ideal.subset_span ⟨(x, y), h, rfl⟩
  | refl x => simp [relationBinomial]
  | symm h ih =>
      simpa [relationBinomial, neg_sub] using (relationIdeal k r).neg_mem ih
  | trans h₁ h₂ ih₁ ih₂ =>
      simpa [relationBinomial] using (relationIdeal k r).add_mem ih₁ ih₂
  | @add w x y z h₁ h₂ ih₁ ih₂ =>
      have h₁' := (relationIdeal k r).mul_mem_left (AddMonoidAlgebra.single y 1) ih₁
      have h₂' := (relationIdeal k r).mul_mem_left (AddMonoidAlgebra.single x 1) ih₂
      convert (relationIdeal k r).add_mem h₁' h₂' using 1
      simp only [relationBinomial, mul_sub, AddMonoidAlgebra.single_mul_single, one_mul]
      rw [add_comm y w, add_comm y x]
      abel

/-- The quotient monoid algebra detects precisely the equivalence classes of monomials. -/
theorem generated_of_relationBinomial_mem (r : Set (M × M)) (x y : M)
    (h : relationBinomial k (x, y) ∈ relationIdeal k r) : generatedCongruence r x y := by
  let c := generatedCongruence r
  let q := AddMonoidAlgebra.mapDomainRingHom k c.mk'
  have hle : relationIdeal k r ≤ RingHom.ker q := by
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨u, v⟩, huv, rfl⟩
    change q (relationBinomial k (u, v)) = 0
    have he : c.mk' u = c.mk' v := c.eq.mpr (AddConGen.Rel.of u v huv)
    simp only [relationBinomial, map_sub]
    simp only [q, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
    rw [he, sub_self]
  have he : AddMonoidAlgebra.single (c.mk' x) (1 : k) =
      AddMonoidAlgebra.single (c.mk' y) (1 : k) := by
    have hz := hle h
    change q (relationBinomial k (x, y)) = 0 at hz
    simp only [relationBinomial, map_sub] at hz
    simp only [q, AddMonoidAlgebra.mapDomainRingHom_apply,
      AddMonoidAlgebra.mapDomain_single] at hz
    exact sub_eq_zero.mp hz
  exact c.eq.mp (AddMonoidAlgebra.single_left_injective one_ne_zero he)

theorem relationBinomial_mem_iff (r : Set (M × M)) (x y : M) :
    relationBinomial k (x, y) ∈ relationIdeal k r ↔ generatedCongruence r x y :=
  ⟨generated_of_relationBinomial_mem k r x y, relationBinomial_mem_of_generated k r x y⟩

theorem generatedCongruence_eq_of_relationIdeal_eq (r s : Set (M × M))
    (h : relationIdeal k r = relationIdeal k s) :
    generatedCongruence r = generatedCongruence s := by
  ext x y
  rw [← relationBinomial_mem_iff k, ← relationBinomial_mem_iff k, h]

theorem generatedCongruence_all_relations (c : AddCon M) :
    generatedCongruence {p : M × M | c p.1 p.2} = c :=
  AddCon.addConGen_of_addCon c

/-- Finite presentability of congruences on a finite free commutative monoid.
The field is only an auxiliary tool; the resulting relations are purely combinatorial. -/
theorem exists_finset_generating_congruence {σ : Type*} [Finite σ]
    (c : AddCon (σ →₀ ℕ)) :
    ∃ s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)),
      generatedCongruence (s : Set _) = c := by
  classical
  let r : Set ((σ →₀ ℕ) × (σ →₀ ℕ)) := {p | c p.1 p.2}
  have hfg : (relationIdeal ℚ r).FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨t, ht, he⟩ := Submodule.fg_span_iff_fg_span_finset_subset
    (relationBinomial ℚ '' r) |>.mp hfg
  obtain ⟨s, hs, hst⟩ := Finset.subset_set_image_iff.mp ht
  refine ⟨s, ?_⟩
  have hI : relationIdeal ℚ r = relationIdeal ℚ (s : Set _) := by
    change Submodule.span _ (relationBinomial ℚ '' r) =
      Submodule.span _ (relationBinomial ℚ '' (s : Set _))
    rw [he, ← hst, Finset.coe_image]
  exact (generatedCongruence_eq_of_relationIdeal_eq ℚ _ _ hI).symm.trans
    (generatedCongruence_all_relations c)

end NS25Lean.Presentation
