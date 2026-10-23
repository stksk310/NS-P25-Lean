import NS25Lean.FourBettiPresentation

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2C
open ChosenBase
variable {Gamma : NumericalSemigroup}

theorem weight_zero_iff (B : Data Gamma) (u : Fin 4 →₀ ℕ) : weight B u = 0 ↔ u = 0 := by
  constructor
  · intro h
    ext j
    have he := fiber_coordinate_le B 0 ⟨u, h⟩ j
    exact Nat.eq_zero_of_le_zero he
  · intro h; simp [h]

theorem positive_coordinate (B : Data Gamma) (u : Fin 4 →₀ ℕ) (hu : 0 < weight B u) :
    ∃ j, 0 < u j := by
  by_contra! hn
  have he : u = 0 := by ext j; exact Nat.eq_zero_of_le_zero (hn j)
  simp [he] at hu

/-- A cut at one component of one degree, together with equality of weights.
Positive translations have a common variable, which makes this an additive congruence. -/
def componentCut (B : Data Gamma) (d : ℕ) (C : FiberComponent B d) : AddCon (Fin 4 →₀ ℕ) where
  r u v := weight B u = weight B v ∧ ∀ (hu : weight B u = d) (hv : weight B v = d),
    ((fiberGraph B d).connectedComponentMk ⟨u, hu⟩ = C ↔
     (fiberGraph B d).connectedComponentMk ⟨v, hv⟩ = C)
  iseqv := ⟨fun _ => ⟨rfl, fun _ _ => Iff.rfl⟩,
    fun h => ⟨h.1.symm, fun hu hv => (h.2 hv hu).symm⟩,
    fun h₁ h₂ => ⟨h₁.1.trans h₂.1, fun hu hv =>
      (h₁.2 hu (h₁.1.symm.trans hu)).trans (h₂.2 (h₁.1.symm.trans hu) hv)⟩⟩
  add' := by
    intro w x y z hw hy
    refine ⟨by simp only [map_add, hw.1, hy.1], ?_⟩
    intro hwy hxz
    by_cases hw0 : weight B w = 0
    · have hx0 := hw.1.symm.trans hw0
      have ew := (weight_zero_iff B w).mp hw0
      have ex := (weight_zero_iff B x).mp hx0
      subst w; subst x
      simpa only [zero_add] using hy.2 (by simpa using hwy) (by simpa using hxz)
    by_cases hy0 : weight B y = 0
    · have hz0 := hy.1.symm.trans hy0
      have ey := (weight_zero_iff B y).mp hy0
      have ez := (weight_zero_iff B z).mp hz0
      subst y; subst z
      simpa only [add_zero] using hw.2 (by simpa using hwy) (by simpa using hxz)
    obtain ⟨i, hi⟩ := positive_coordinate B x (by omega)
    obtain ⟨j, hj⟩ := positive_coordinate B y (Nat.pos_of_ne_zero hy0)
    let a : FactorizationFiber B d := ⟨w + y, hwy⟩
    let b : FactorizationFiber B d := ⟨x + y, by simpa only [map_add, hy.1] using hxz⟩
    let c : FactorizationFiber B d := ⟨x + z, hxz⟩
    have hab := same_component_of_shared B d a b j
      (by dsimp [a]; omega)
      (by dsimp [b]; omega)
    have hbc := same_component_of_shared B d b c i
      (by dsimp [b]; omega)
      (by dsimp [c]; omega)
    exact (hab.trans hbc).congr_left

end NS25Lean.L2C
