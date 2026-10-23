import NS25Lean.StandardRho

set_option linter.style.header false

/-! An arbitrary pivot in a minimal four-generator family. No order or multiplicity
assumption is made. The swap is part of the model, not an implicit relabeling. -/

noncomputable section
namespace NS25Lean.ChosenBase
open FourGeneratedBridge ToricPresentation

structure Data (Gamma : NumericalSemigroup) where
  family : Fin 4 → Gamma.toAddSubmonoid
  generates : AddSubmonoid.closure (Set.range (fun i => (family i).val)) = Gamma.toAddSubmonoid
  positive : ∀ i, 0 < (family i).val
  minimal : ∀ i, (family i).val ∉
    AddSubmonoid.closure ((fun j => (family j).val) '' {j | j ≠ i})
  pivot : Fin 4

variable {Gamma : NumericalSemigroup}

def Data.ofFourTuple (Gamma : NumericalSemigroup) (m a b c : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m a b c) (i : Fin 4) : Data Gamma where
  family := fourDegrees Gamma m a b c h
  generates := (Presentation.fourDegrees_minimal_data Gamma m a b c h).1
  positive := (Presentation.fourDegrees_minimal_data Gamma m a b c h).2.1
  minimal := (Presentation.fourDegrees_minimal_data Gamma m a b c h).2.2
  pivot := i

def Data.order (B : Data Gamma) : Fin 4 ≃ Fin 4 := Equiv.swap 0 B.pivot
def Data.degrees (B : Data Gamma) : Fin 4 → Gamma.toAddSubmonoid := B.family ∘ B.order
def Data.q (B : Data Gamma) : Gamma.toAddSubmonoid := B.family B.pivot
def Data.H (B : Data Gamma) : AddSubmonoid ℕ :=
  AddSubmonoid.closure (Set.range (fun j : Fin 3 => (B.degrees j.succ).val))
def Data.K (B : Data Gamma) : Set ℕ := aperyTail Gamma.toAddSubmonoid B.H B.q.val
def Data.apery (B : Data Gamma) : Set ℕ := aperySet Gamma.toAddSubmonoid B.q.val
def Data.tailDegrees (B : Data Gamma) : Fin 3 → B.H :=
  fun j => ⟨(B.degrees j.succ).val, AddSubmonoid.subset_closure ⟨j, rfl⟩⟩

@[simp] theorem Data.degrees_zero (B : Data Gamma) : B.degrees 0 = B.q := by
  simp [Data.degrees, Data.order, Data.q]

theorem Data.q_positive (B : Data Gamma) : 0 < B.q.val := B.positive B.pivot

theorem Data.degrees_positive (B : Data Gamma) : ∀ i, 0 < (B.degrees i).val :=
  fun i => B.positive (B.order i)

theorem Data.degrees_generate_nat (B : Data Gamma) :
    AddSubmonoid.closure (Set.range (fun i => (B.degrees i).val)) = Gamma.toAddSubmonoid := by
  have he : Set.range (fun i => (B.degrees i).val) = Set.range (fun i => (B.family i).val) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨B.order i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨B.order.symm i, by simp [Data.degrees]⟩
  rw [he, B.generates]

theorem Data.degrees_minimal (B : Data Gamma) (i : Fin 4) :
    (B.degrees i).val ∉ AddSubmonoid.closure ((fun j => (B.degrees j).val) '' {j | j ≠ i}) := by
  intro hi
  apply B.minimal (B.order i)
  apply AddSubmonoid.closure_mono _ hi
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨B.order j, fun he => hj (B.order.injective he), rfl⟩

theorem Data.degrees_generate (B : Data Gamma) :
    AddSubmonoid.closure (Set.range B.degrees) = ⊤ :=
  subtype_degrees_generate _ _ B.degrees_generate_nat.symm

theorem Data.tailDegrees_generate (B : Data Gamma) :
    AddSubmonoid.closure (Set.range B.tailDegrees) = ⊤ :=
  subtype_degrees_generate _ _ rfl

theorem Data.H_le (B : Data Gamma) : B.H ≤ Gamma.toAddSubmonoid := by
  apply AddSubmonoid.closure_le.mpr
  rintro _ ⟨j, rfl⟩
  exact (B.degrees j.succ).property

/-- The three tail indices are exactly all original indices except the chosen pivot. -/
theorem Data.tail_range (B : Data Gamma) :
    Set.range (fun j : Fin 3 => (B.degrees j.succ).val) =
      (fun i => (B.family i).val) '' {i | i ≠ B.pivot} := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨B.order j.succ, ?_, rfl⟩
    intro he
    have hz : B.order 0 = B.pivot := by simp [Data.order]
    have := B.order.injective (he.trans hz.symm)
    exact Fin.succ_ne_zero j this
  · rintro ⟨i, hi, rfl⟩
    have hn : B.order.symm i ≠ 0 := by
      intro he
      have := congrArg B.order he
      simp only [Equiv.apply_symm_apply, Data.order, Equiv.swap_apply_left] at this
      exact hi this
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hn
    refine ⟨j, ?_⟩
    change (B.family (B.order j.succ)).val = _
    rw [hj, B.order.apply_symm_apply]

theorem Data.generatedOver (B : Data Gamma) :
    IsGeneratedOver Gamma.toAddSubmonoid B.H B.q.val := by
  intro x hx
  rw [← B.degrees_generate_nat] at hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨1, 0, B.H.zero_mem, by simp⟩
      · exact ⟨0, (B.degrees j.succ).val, AddSubmonoid.subset_closure ⟨j, rfl⟩, by simp⟩
  | zero => exact ⟨0, 0, B.H.zero_mem, by simp⟩
  | add a b ha hb iha ihb =>
      obtain ⟨r, x, hx, rfl⟩ := iha
      obtain ⟨s, y, hy, rfl⟩ := ihb
      exact ⟨r + s, x + y, B.H.add_mem hx hy, by ring⟩

/-- A1, with integer-subtraction semantics inherited from the frozen Apéry predicates. -/
theorem Data.apery_eq_compl (B : Data Gamma) :
    B.apery = {x : ℕ | x ∈ B.H ∧ x ∉ B.K} :=
  (relative_compl_aperyTail_eq_aperySet B.q_positive B.q.property B.H_le B.generatedOver).symm

theorem Data.apery_finite (B : Data Gamma) : B.apery.Finite :=
  aperySet_finite Gamma B.q.val

theorem Data.rho_eq_toricGeneratorNumber (k : Type*) [Field k] (B : Data Gamma) :
    Presentation.rho Gamma = toricGeneratorNumber k Gamma.toAddSubmonoid B.degrees := by
  rw [Presentation.rho_eq_presentationNumber_of_minimal_degrees Gamma B.degrees
    B.degrees_generate_nat B.degrees_positive B.degrees_minimal]
  exact Presentation.presentationNumber_eq_toricGeneratorNumber k _ _ B.degrees_positive

/-- Every intrinsically chosen minimal generator can be used as the pivot. -/
def Data.ofAtom (Gamma : NumericalSemigroup) (m a b c : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m a b c) (q : Presentation.Atom Gamma) : Data Gamma :=
  let hd := Presentation.fourDegrees_minimal_data Gamma m a b c h
  Data.ofFourTuple Gamma m a b c h
    ((Presentation.degreeAtomEquiv Gamma (fourDegrees Gamma m a b c h)
      hd.1 hd.2.1 hd.2.2).symm q)

theorem Data.ofAtom_q (Gamma : NumericalSemigroup) (m a b c : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m a b c) (q : Presentation.Atom Gamma) :
    (Data.ofAtom Gamma m a b c h q).q.val = q.val := by
  let hd := Presentation.fourDegrees_minimal_data Gamma m a b c h
  let e := Presentation.degreeAtomEquiv Gamma (fourDegrees Gamma m a b c h) hd.1 hd.2.1 hd.2.2
  exact congrArg (fun x : Presentation.Atom Gamma => x.val) (e.apply_symm_apply q)

end NS25Lean.ChosenBase
