import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option linter.style.header false

/-! Toric kernels over an arbitrary field. Generator numbers below are the
actual minimum cardinalities of generating sets, using mathlib's spanFinrank.
They are deliberately not named rho: the presentation comparison is separate. -/

noncomputable section
namespace NS25Lean.ToricPresentation

variable (k : Type*) [Field k]

abbrev SemigroupAlgebra (H : AddSubmonoid ℕ) := AddMonoidAlgebra k H
abbrev Poly (n : ℕ) := MvPolynomial (Fin n) k

instance semigroupUniqueSums (H : AddSubmonoid ℕ) : UniqueSums H :=
  UniqueSums.of_injective_addHom H.subtype.toAddHom Subtype.val_injective inferInstance

def toricMap {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H) :
    Poly k n →ₐ[k] SemigroupAlgebra k H :=
  MvPolynomial.aeval (fun i => AddMonoidAlgebra.single (w i) 1)

def toricIdeal {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H) : Ideal (Poly k n) :=
  RingHom.ker (toricMap k H w).toRingHom

@[simp] theorem toricMap_X {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H) (i : Fin n) :
    toricMap k H w (MvPolynomial.X i) = AddMonoidAlgebra.single (w i) 1 := by
  simp [toricMap]

theorem toricMap_X_ne_zero {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H) (i : Fin n) :
    toricMap k H w (MvPolynomial.X i) ≠ 0 := by
  simp

theorem X_not_mem_toricIdeal {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H) (i : Fin n) :
    MvPolynomial.X i ∉ toricIdeal k H w :=
  toricMap_X_ne_zero k H w i

theorem X_mul_mem_toricIdeal_iff {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H)
    (i : Fin n) (f : Poly k n) :
    MvPolynomial.X i * f ∈ toricIdeal k H w ↔ f ∈ toricIdeal k H w := by
  change toricMap k H w (MvPolynomial.X i * f) = 0 ↔ toricMap k H w f = 0
  rw [map_mul, mul_eq_zero]
  exact or_iff_right (toricMap_X_ne_zero k H w i)

/-- The paper's intersection lemma, proved directly from the toric kernel. -/
theorem toricIdeal_inf_span_X {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H)
    (i : Fin n) :
    toricIdeal k H w ⊓ Ideal.span {MvPolynomial.X i} =
      Ideal.span {MvPolynomial.X i} * toricIdeal k H w := by
  ext f
  constructor
  · rintro ⟨hf, hx⟩
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hx
    exact Ideal.mem_span_singleton_mul.mpr
      ⟨g, (X_mul_mem_toricIdeal_iff k H w i g).mp hf, rfl⟩
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Ideal.mem_span_singleton_mul.mp hf
    exact ⟨(X_mul_mem_toricIdeal_iff k H w i g).mpr hg,
      Ideal.mem_span_singleton.mpr ⟨g, rfl⟩⟩

theorem toricIdeal_fg {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H) :
    (toricIdeal k H w).FG := Ideal.fg_of_isNoetherianRing _

def toricGeneratorNumber {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H) : ℕ :=
  (toricIdeal k H w).spanFinrank

theorem toricGeneratorNumber_attained {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H) :
    ∃ s : Finset (Poly k n), s.card = toricGeneratorNumber k H w ∧
      Submodule.span (Poly k n) (s : Set (Poly k n)) = toricIdeal k H w := by
  exact Submodule.FG.exists_span_finset_card_eq_spanFinrank (toricIdeal_fg k H w)

/-- A generating family of semigroup degrees gives a surjective toric map. -/
theorem toricMap_surjective {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H)
    (hgen : AddSubmonoid.closure (Set.range w) = ⊤) :
    Function.Surjective (toricMap k H w) := by
  have hb : ∀ h : H, AddMonoidAlgebra.single h (1 : k) ∈ (toricMap k H w).range := by
    intro h
    have hh : h ∈ AddSubmonoid.closure (Set.range w) := by rw [hgen]; trivial
    induction hh using AddSubmonoid.closure_induction with
    | mem h hh =>
        obtain ⟨i, rfl⟩ := hh
        exact ⟨MvPolynomial.X i, toricMap_X k H w i⟩
    | zero => exact ⟨1, map_one _⟩
    | add a b ha hb iha ihb =>
        simpa using (toricMap k H w).range.mul_mem iha ihb
  intro f
  have hf : f ∈ (toricMap k H w).range := by
    induction f using AddMonoidAlgebra.induction_on with
    | of h => exact hb h
    | add f g hf hg => exact (toricMap k H w).range.add_mem hf hg
    | smul r f hf => exact (toricMap k H w).range.smul_mem hf r
  exact hf

def toricQuotientEquiv {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H)
    (hgen : AddSubmonoid.closure (Set.range w) = ⊤) :
    (Poly k n ⧸ toricIdeal k H w) ≃+* SemigroupAlgebra k H :=
  RingHom.quotientKerEquivOfSurjective (toricMap_surjective k H w hgen)

end NS25Lean.ToricPresentation
