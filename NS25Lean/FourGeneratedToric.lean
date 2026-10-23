import NS25Lean.TailMonomialIdeal
import Mathlib.Data.Fin.VecNotation

set_option linter.style.header false

noncomputable section
namespace NS25Lean.ToricPresentation
open FourGeneratedBridge
variable (k : Type*) [Field k]

theorem subtype_degrees_generate {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H)
    (hgen : H = AddSubmonoid.closure (Set.range (fun i => (w i).val))) :
    AddSubmonoid.closure (Set.range w) = ⊤ := by
  have hle : H ≤ (AddSubmonoid.closure (Set.range w)).map H.subtype := by
    conv_lhs => rw [hgen]
    apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨w i, AddSubmonoid.subset_closure ⟨i, rfl⟩, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  have hyx : y = x := Subtype.ext he
  simpa [hyx] using hy

def tailDegrees (n₁ n₂ n₃ : ℕ) : Fin 3 → generatedThree n₁ n₂ n₃ :=
  fun i => ⟨![n₁, n₂, n₃] i, by
    apply AddSubmonoid.subset_closure
    fin_cases i <;> simp⟩

def fourDegrees (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) : Fin 4 → Gamma.toAddSubmonoid :=
  fun i => ⟨![m, n₁, n₂, n₃] i, by
    rw [h.generated]
    apply AddSubmonoid.subset_closure
    fin_cases i <;> simp⟩

theorem tailDegrees_generate (n₁ n₂ n₃ : ℕ) :
    AddSubmonoid.closure (Set.range (tailDegrees n₁ n₂ n₃)) = ⊤ := by
  apply subtype_degrees_generate
  unfold generatedThree
  congr 1
  ext a
  simp [tailDegrees, Matrix.range_cons, Matrix.range_empty]
  tauto

theorem fourDegrees_generate (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    AddSubmonoid.closure (Set.range (fourDegrees Gamma m n₁ n₂ n₃ h)) = ⊤ := by
  apply subtype_degrees_generate
  calc
    Gamma.toAddSubmonoid = generatedFour m n₁ n₂ n₃ := h.generated
    _ = _ := by
      unfold generatedFour
      congr 1
      ext a
      simp [fourDegrees, Matrix.range_cons, Matrix.range_empty]
      tauto

theorem fourGenerated_tailMonomial_generatorNumber_le (Gamma : NumericalSemigroup)
    (m n₁ n₂ n₃ : ℕ) (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    (tailMonomialIdeal k Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m).spanFinrank ≤
      toricGeneratorNumber k Gamma.toAddSubmonoid (fourDegrees Gamma m n₁ n₂ n₃ h) := by
  have hle : generatedThree n₁ n₂ n₃ ≤ Gamma.toAddSubmonoid := by
    rw [h.generated]
    exact generatedThree_le_generatedFour m n₁ n₂ n₃
  apply tailMonomialIdeal_generatorNumber_le k Gamma.toAddSubmonoid
    (generatedThree n₁ n₂ n₃) hle (fourDegrees Gamma m n₁ n₂ n₃ h)
    (tailDegrees n₁ n₂ n₃)
  · intro i
    apply Subtype.ext
    fin_cases i <;> rfl
  · exact fourDegrees_generate Gamma m n₁ n₂ n₃ h
  · exact tailDegrees_generate n₁ n₂ n₃

end NS25Lean.ToricPresentation
