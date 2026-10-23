import NS25Lean.PresentationToric

set_option linter.style.header false

/-!
# Intrinsic factorization-presentation number

The index set consists of the actual indecomposable nonzero semigroup elements.
Thus `rho` is defined from finite congruence presentations without a chosen
ordering or coefficient field. The common-cardinality theorem for arbitrary
inclusion-minimal presentations is not built into this definition.
-/

noncomputable section
namespace NS25Lean.Presentation
open FourGeneratedBridge ToricPresentation

def IsAtom (Gamma : NumericalSemigroup) (x : ℕ) : Prop :=
  x ∈ Gamma ∧ x ≠ 0 ∧ ∀ a b : ℕ, a ∈ Gamma → b ∈ Gamma →
    x = a + b → a = 0 ∨ b = 0

abbrev Atom (Gamma : NumericalSemigroup) := {x : ℕ // IsAtom Gamma x}

theorem atoms_finite (Gamma : NumericalSemigroup) : Set.Finite {x | IsAtom Gamma x} := by
  obtain ⟨c, hc⟩ := Gamma.exists_conductor
  apply (Set.finite_lt_nat (2 * (c + 1))).subset
  intro x hx
  change x < 2 * (c + 1)
  by_contra hlt
  have ha := hc (c + 1) (by omega)
  have hb := hc (x - (c + 1)) (by omega)
  rcases hx.2.2 (c + 1) (x - (c + 1)) ha hb (by omega) with hz | hz <;> omega

instance finiteAtom (Gamma : NumericalSemigroup) : Finite (Atom Gamma) :=
  (atoms_finite Gamma).to_subtype

theorem atoms_generate (Gamma : NumericalSemigroup) :
    AddSubmonoid.closure {x | IsAtom Gamma x} = Gamma.toAddSubmonoid := by
  apply le_antisymm
  · exact AddSubmonoid.closure_le.mpr (fun x hx => hx.1)
  · intro x
    induction x using Nat.strong_induction_on with
    | h x ih =>
        intro hx
        by_cases hx0 : x = 0
        · subst x; exact AddSubmonoid.zero_mem _
        by_cases ha : IsAtom Gamma x
        · exact AddSubmonoid.subset_closure ha
        have hn : ¬ ∀ a b : ℕ, a ∈ Gamma → b ∈ Gamma →
            x = a + b → a = 0 ∨ b = 0 := fun hh => ha ⟨hx, hx0, hh⟩
        push Not at hn
        obtain ⟨a, b, ham, hbm, he, ha0, hb0⟩ := hn
        rw [he]
        exact AddSubmonoid.add_mem _ (ih a (by omega) ham) (ih b (by omega) hbm)

def atomDegrees (Gamma : NumericalSemigroup) : Atom Gamma → Gamma.toAddSubmonoid :=
  fun x => ⟨x.val, x.property.1⟩

theorem atomDegrees_generate (Gamma : NumericalSemigroup) :
    AddSubmonoid.closure (Set.range (atomDegrees Gamma)) = ⊤ := by
  have hle : Gamma.toAddSubmonoid ≤
      (AddSubmonoid.closure (Set.range (atomDegrees Gamma))).map Gamma.toAddSubmonoid.subtype := by
    conv_lhs => rw [← atoms_generate Gamma]
    apply AddSubmonoid.closure_le.mpr
    intro x hx
    exact ⟨⟨x, hx.1⟩, AddSubmonoid.subset_closure ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  have hxy : y = x := Subtype.ext he
  simpa [hxy] using hy

theorem factorizationMap_surjective {σ H : Type*} [AddCommMonoid H] (w : σ → H)
    (hgen : AddSubmonoid.closure (Set.range w) = ⊤) : Function.Surjective (factorizationMap w) := by
  intro x
  have hx : x ∈ AddSubmonoid.closure (Set.range w) := hgen ▸ trivial
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨Finsupp.single i 1, by simp⟩
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb iha ihb =>
      obtain ⟨u, rfl⟩ := iha
      obtain ⟨v, rfl⟩ := ihb
      exact ⟨u + v, map_add _ _ _⟩

/-- Intrinsic least finite congruence-presentation cardinality on the canonical atoms.
Certification that every inclusion-minimal presentation has this size is separate. -/
def rho (Gamma : NumericalSemigroup) : ℕ := presentationNumber (atomDegrees Gamma)

theorem rho_attained (Gamma : NumericalSemigroup) :
    ∃ s, IsMinimalPresentation (atomDegrees Gamma) s ∧ s.card = rho Gamma :=
  exists_minimalPresentation (atomDegrees Gamma)

theorem rho_le_card_of_presentation (Gamma : NumericalSemigroup)
    (s : Finset ((Atom Gamma →₀ ℕ) × (Atom Gamma →₀ ℕ)))
    (hs : IsPresentation (atomDegrees Gamma) s) : rho Gamma ≤ s.card :=
  presentationNumber_le_card _ _ hs

theorem atom_mem_range {σ : Type*} (Gamma : NumericalSemigroup) (w : σ → ℕ)
    (hgen : AddSubmonoid.closure (Set.range w) = Gamma.toAddSubmonoid)
    {x : ℕ} (hx : IsAtom Gamma x) : x ∈ Set.range w := by
  have hm : x ∈ AddSubmonoid.closure (Set.range w) := hgen.symm ▸ hx.1
  revert hx
  induction hm using AddSubmonoid.closure_induction with
  | mem x hm => intro _; exact hm
  | zero => intro hx; exact (hx.2.1 rfl).elim
  | add a b ha hb iha ihb =>
      intro hx
      have ham : a ∈ Gamma.toAddSubmonoid := hgen ▸ ha
      have hbm : b ∈ Gamma.toAddSubmonoid := hgen ▸ hb
      rcases hx.2.2 a b ham hbm rfl with hz | hz
      · subst a
        simpa using ihb (by simpa using hx)
      · subst b
        exact iha (by simpa using hx)

theorem mem_closure_others_of_lt {σ : Type*} (w : σ → ℕ) (i : σ)
    {x : ℕ} (hx : x ∈ AddSubmonoid.closure (Set.range w)) (hlt : x < w i) :
    x ∈ AddSubmonoid.closure (w '' {j | j ≠ i}) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact AddSubmonoid.subset_closure ⟨j, (by intro he; subst j; omega), rfl⟩
  | zero => exact AddSubmonoid.zero_mem _
  | add a b ha hb iha ihb => exact AddSubmonoid.add_mem _ (iha (by omega)) (ihb (by omega))

theorem minimal_degree_isAtom {σ : Type*} (Gamma : NumericalSemigroup) (w : σ → ℕ)
    (hgen : AddSubmonoid.closure (Set.range w) = Gamma.toAddSubmonoid)
    (i : σ) (hpos : 0 < w i) (hmin : w i ∉ AddSubmonoid.closure (w '' {j | j ≠ i})) :
    IsAtom Gamma (w i) := by
  have hm : w i ∈ Gamma.toAddSubmonoid := hgen ▸ AddSubmonoid.subset_closure ⟨i, rfl⟩
  refine ⟨hm, by omega, ?_⟩
  intro a b ha hb he
  by_contra! hn
  apply hmin
  rw [he]
  exact AddSubmonoid.add_mem _
    (mem_closure_others_of_lt w i (hgen.symm ▸ ha) (by omega))
    (mem_closure_others_of_lt w i (hgen.symm ▸ hb) (by omega))

def degreeAtomEquiv {σ : Type*} (Gamma : NumericalSemigroup) (w : σ → Gamma.toAddSubmonoid)
    (hgen : AddSubmonoid.closure (Set.range (fun i => (w i).val)) = Gamma.toAddSubmonoid)
    (hpos : ∀ i, 0 < (w i).val)
    (hmin : ∀ i, (w i).val ∉ AddSubmonoid.closure ((fun j => (w j).val) '' {j | j ≠ i})) :
    σ ≃ Atom Gamma :=
  Equiv.ofBijective (fun i => ⟨(w i).val, minimal_degree_isAtom Gamma _ hgen i (hpos i) (hmin i)⟩)
    ⟨by
      intro i j he
      by_contra hij
      apply hmin i
      have hv : (w i).val = (w j).val := congrArg (fun x : Atom Gamma => x.val) he
      exact hv ▸ AddSubmonoid.subset_closure ⟨j, Ne.symm hij, rfl⟩,
    by
      intro x
      obtain ⟨i, hi⟩ := atom_mem_range Gamma _ hgen x.property
      exact ⟨i, Subtype.ext hi⟩⟩

theorem rho_eq_presentationNumber_of_minimal_degrees {σ : Type*} [Finite σ]
    (Gamma : NumericalSemigroup) (w : σ → Gamma.toAddSubmonoid)
    (hgen : AddSubmonoid.closure (Set.range (fun i => (w i).val)) = Gamma.toAddSubmonoid)
    (hpos : ∀ i, 0 < (w i).val)
    (hmin : ∀ i, (w i).val ∉ AddSubmonoid.closure ((fun j => (w j).val) '' {j | j ≠ i})) :
    rho Gamma = presentationNumber w := by
  apply presentationNumber_reindex (degreeAtomEquiv Gamma w hgen hpos hmin)
  intro i
  rfl

theorem fourDegrees_minimal_data (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    let w := fourDegrees Gamma m n₁ n₂ n₃ h
    AddSubmonoid.closure (Set.range (fun i => (w i).val)) = Gamma.toAddSubmonoid ∧
      (∀ i, 0 < (w i).val) ∧
      (∀ i, (w i).val ∉ AddSubmonoid.closure ((fun j => (w j).val) '' {j | j ≠ i})) := by
  dsimp only
  have himg : ∀ i : Fin 4,
      (fun j : Fin 4 => ![m, n₁, n₂, n₃] j) '' {j | j ≠ i} =
        ![{n₁, n₂, n₃}, {m, n₂, n₃}, {m, n₁, n₃}, {m, n₁, n₂}] i := by
    intro i
    fin_cases i <;> ext x <;> simp [Set.mem_image, Fin.exists_fin_succ] <;> tauto
  refine ⟨?_, ?_, ?_⟩
  · change AddSubmonoid.closure (Set.range ![m, n₁, n₂, n₃]) = Gamma.toAddSubmonoid
    rw [h.generated]
    unfold generatedFour
    congr 1
    ext x
    simp
    tauto
  · intro i
    fin_cases i
    · exact h.m_pos
    · exact h.n₁_pos
    · exact h.n₂_pos
    · exact h.n₃_pos
  · intro i
    fin_cases i
    · simpa [fourDegrees, himg, generatedThree] using h.m_minimal
    · simpa [fourDegrees, himg, generatedThree] using h.n₁_minimal
    · simpa [fourDegrees, himg, generatedThree] using h.n₂_minimal
    · simpa [fourDegrees, himg, generatedThree] using h.n₃_minimal

/-- The intrinsic congruence invariant agrees with the minimum presentation size
for every displayed minimal four-tuple, including any ordering. -/
theorem rho_eq_four_presentationNumber (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    rho Gamma = presentationNumber (fourDegrees Gamma m n₁ n₂ n₃ h) := by
  obtain ⟨hg, hp, hm⟩ := fourDegrees_minimal_data Gamma m n₁ n₂ n₃ h
  exact rho_eq_presentationNumber_of_minimal_degrees Gamma _ hg hp hm

theorem fourGenerated_toricGeneratorNumber_le_rho (k : Type*) [Field k]
    (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    toricGeneratorNumber k Gamma.toAddSubmonoid (fourDegrees Gamma m n₁ n₂ n₃ h) ≤ rho Gamma := by
  rw [rho_eq_four_presentationNumber Gamma m n₁ n₂ n₃ h]
  exact toricGeneratorNumber_le_presentationNumber k _ _

end NS25Lean.Presentation
