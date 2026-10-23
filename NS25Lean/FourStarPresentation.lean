import NS25Lean.FourComponentCut

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2C
open ChosenBase Presentation Classical
variable {Gamma : NumericalSemigroup}

def componentRepresentative (B : Data Gamma) (d : ℕ) (C : FiberComponent B d) :
    FactorizationFiber B d := Classical.choose C.exists_rep

theorem representative_component (B : Data Gamma) (d : ℕ) (C : FiberComponent B d) :
    (fiberGraph B d).connectedComponentMk (componentRepresentative B d C) = C :=
  Classical.choose_spec C.exists_rep

def rootComponent (B : Data Gamma) (d : bettiDegrees B) : FiberComponent B d.val := by
  haveI := (betti_iff_nontrivial B d.val).mp ((mem_bettiDegrees B d.val).mp d.property)
  exact Classical.arbitrary _

def StarIndex (B : Data Gamma) :=
  Sigma (fun d : bettiDegrees B => {C : FiberComponent B d.val // C ≠ rootComponent B d})

instance finiteStarIndex (B : Data Gamma) : Finite (StarIndex B) := by
  unfold StarIndex
  infer_instance

def starRelation (B : Data Gamma) (x : StarIndex B) : (Fin 4 →₀ ℕ) × (Fin 4 →₀ ℕ) :=
  ((componentRepresentative B x.1.val (rootComponent B x.1)).val,
    (componentRepresentative B x.1.val x.2.val).val)

theorem starRelation_injective (B : Data Gamma) : Function.Injective (starRelation B) := by
  rintro ⟨⟨d, hd⟩, C, hC⟩ ⟨⟨e, he⟩, E, hE⟩ h
  have hde : d = e := by
    have h' := congrArg (fun p => weight B p.1) h
    exact (componentRepresentative B d (rootComponent B ⟨d, hd⟩)).property.symm.trans
      (h'.trans (componentRepresentative B e (rootComponent B ⟨e, he⟩)).property)
  subst e
  have hreps := congrArg Prod.snd h
  have hCE : C = E := by
    rw [← representative_component B d C, ← representative_component B d E]
    apply congrArg
    exact Subtype.ext hreps
  subst E
  rfl

def starPresentation (B : Data Gamma) : Finset ((Fin 4 →₀ ℕ) × (Fin 4 →₀ ℕ)) :=
  letI := Fintype.ofFinite (StarIndex B)
  Finset.univ.image (starRelation B)

@[simp] theorem mem_starPresentation (B : Data Gamma) (p : (Fin 4 →₀ ℕ) × (Fin 4 →₀ ℕ)) :
    p ∈ starPresentation B ↔ ∃ x, starRelation B x = p := by
  letI := Fintype.ofFinite (StarIndex B)
  simp [starPresentation]

theorem starPresentation_card (B : Data Gamma) :
    (starPresentation B).card = ∑ d ∈ bettiDegrees B, (componentCount B d - 1) := by
  letI := Fintype.ofFinite (StarIndex B)
  letI (d : bettiDegrees B) := Fintype.ofFinite (FiberComponent B d.val)
  rw [starPresentation, Finset.card_image_of_injective _ (starRelation_injective B), Finset.card_univ]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (Sigma (fun d : bettiDegrees B => {C : FiberComponent B d.val // C ≠ rootComponent B d})) = _
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_sigma]
  calc
    _ = ∑ d : bettiDegrees B, (componentCount B d.val - 1) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Fintype.card_subtype]
      have he : Finset.univ.filter (fun C : FiberComponent B d.val => C ≠ rootComponent B d) =
          Finset.univ.erase (rootComponent B d) := by ext C; simp [and_comm]
      rw [he, Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp [componentCount, Nat.card_eq_fintype_card]
    _ = _ := Finset.sum_coe_sort (bettiDegrees B) (fun d => componentCount B d - 1)

theorem starPresentation_generates (B : Data Gamma) (d : ℕ)
    (u v : Fin 4 →₀ ℕ) (hu : weight B u = d) (hv : weight B v = d) :
    generatedCongruence (starPresentation B : Set _) u v := by
  induction d using Nat.strong_induction_on generalizing u v with
  | h d ih =>
    let c : AddCon (Fin 4 →₀ ℕ) := generatedCongruence (starPresentation B : Set _)
    by_cases hd : Betti B d
    · let D : bettiDegrees B := ⟨d, (mem_bettiDegrees B d).mpr hd⟩
      let R := componentRepresentative B d (rootComponent B D)
      have hroot (a : FactorizationFiber B d) : c R.val a.val := by
        let C := (fiberGraph B d).connectedComponentMk a
        let r := componentRepresentative B d C
        have hlow : c r.val a.val := connected_generated_lower B d c ih r a
          (representative_component B d C)
        by_cases hC : C = rootComponent B D
        · have he : r = R := congrArg (componentRepresentative B d) hC
          exact he ▸ hlow
        · have hr : c R.val r.val := AddConGen.Rel.of _ _
            ((mem_starPresentation B _).mpr ⟨⟨D, C, hC⟩, rfl⟩)
          exact c.trans hr hlow
      exact c.trans (c.symm (hroot ⟨u, hu⟩)) (hroot ⟨v, hv⟩)
    · haveI : Subsingleton (FiberComponent B d) :=
        not_nontrivial_iff_subsingleton.mp (fun h => hd ((betti_iff_nontrivial B d).mpr h))
      exact connected_generated_lower B d c ih ⟨u, hu⟩ ⟨v, hv⟩ (Subsingleton.elim _ _)

theorem starPresentation_isPresentation (B : Data Gamma) :
    IsPresentation B.family (starPresentation B) := by
  apply le_antisymm
  · apply AddCon.addConGen_le.mpr
    intro u v huv
    obtain ⟨x, he⟩ := (mem_starPresentation B (u, v)).mp huv
    have hw : weight B u = weight B v := by
      have h₁ := (componentRepresentative B x.1.val (rootComponent B x.1)).property
      have h₂ := (componentRepresentative B x.1.val x.2.val).property
      cases he
      exact h₁.trans h₂.symm
    apply Subtype.ext
    simpa only [← weight_eq_degree] using hw
  · intro u v he
    apply starPresentation_generates B (weight B u) u v rfl
    have he' := congrArg Subtype.val he
    simpa only [← weight_eq_degree] using he'.symm

theorem starRelation_not_cut (B : Data Gamma) (x : StarIndex B) :
    ¬ componentCut B x.1.val x.2.val (starRelation B x).1 (starRelation B x).2 := by
  intro h
  have hi := h.2 (componentRepresentative B x.1.val (rootComponent B x.1)).property
    (componentRepresentative B x.1.val x.2.val).property
  have hright : (fiberGraph B x.1.val).connectedComponentMk
      ⟨(starRelation B x).2, (componentRepresentative B x.1.val x.2.val).property⟩ = x.2.val :=
    representative_component B x.1.val x.2.val
  have hleft := hi.mpr hright
  have he := (representative_component B x.1.val (rootComponent B x.1)).symm.trans hleft
  exact x.2.property he.symm

theorem other_starRelation_cut (B : Data Gamma) (x y : StarIndex B) (hne : x ≠ y) :
    componentCut B x.1.val x.2.val (starRelation B y).1 (starRelation B y).2 := by
  refine ⟨(componentRepresentative B y.1.val (rootComponent B y.1)).property.trans
    (componentRepresentative B y.1.val y.2.val).property.symm, ?_⟩
  intro h₁ h₂
  have hdeg : y.1 = x.1 := Subtype.ext
    ((componentRepresentative B y.1.val (rootComponent B y.1)).property.symm.trans h₁)
  rcases x with ⟨d, C, hC⟩
  rcases y with ⟨e, E, hE⟩
  dsimp at hdeg
  subst e
  have hCE : C ≠ E := by intro h; subst E; exact hne rfl
  change ((fiberGraph B d.val).connectedComponentMk
    (componentRepresentative B d.val (rootComponent B d)) = C ↔
    (fiberGraph B d.val).connectedComponentMk (componentRepresentative B d.val E) = C)
  rw [representative_component, representative_component]
  exact iff_of_false (Ne.symm hC) (Ne.symm hCE)

theorem starPresentation_isMinimal (B : Data Gamma) :
    IsMinimalPresentation B.family (starPresentation B) := by
  refine ⟨starPresentation_isPresentation B, ?_⟩
  intro t hts ht p hp
  obtain ⟨x, rfl⟩ := (mem_starPresentation B p).mp hp
  by_contra hn
  have hle : generatedCongruence (t : Set _) ≤ componentCut B x.1.val x.2.val := by
    apply AddCon.addConGen_le.mpr
    intro u v huv
    obtain ⟨y, hy⟩ := (mem_starPresentation B (u, v)).mp (hts huv)
    have hne : x ≠ y := by intro he; subst y; exact hn (hy ▸ huv)
    simpa only [hy] using other_starRelation_cut B x y hne
  have hr : generatedCongruence (t : Set _) (starRelation B x).1 (starRelation B x).2 := by
    rw [ht]
    apply Subtype.ext
    rw [← weight_eq_degree, ← weight_eq_degree]
    exact (componentRepresentative B x.1.val (rootComponent B x.1)).property.trans
      (componentRepresentative B x.1.val x.2.val).property.symm
  exact starRelation_not_cut B x (hle hr)

/-- Standard rho--Betti formula, from an independently constructed ordinary
inclusion-minimal congruence presentation and the frozen intrinsic rho bridge. -/
theorem rho_eq_betti_sum (B : Data Gamma) :
    Presentation.rho Gamma = ∑ d ∈ bettiDegrees B, (componentCount B d - 1) := by
  rw [rho_eq_presentationNumber_of_minimal_degrees Gamma B.family B.generates B.positive B.minimal]
  exact (card_eq_presentationNumber_of_minimal Gamma.toAddSubmonoid B.family B.positive
    (starPresentation B) (starPresentation_isMinimal B)).symm.trans (starPresentation_card B)

end NS25Lean.L2C
