import NS25Lean.ToricPresentation
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option linter.style.header false

noncomputable section
namespace NS25Lean.ToricPresentation
variable (k : Type*) [Field k]

/-- Setting the first variable to zero, using the polynomial-in-one-variable equivalence. -/
def specialization : Poly k 4 →+* Poly k 3 :=
  Polynomial.constantCoeff.comp (MvPolynomial.finSuccEquiv k 3).toRingHom

@[simp] theorem specialization_X_zero :
    specialization k (MvPolynomial.X 0) = 0 := by
  simp [specialization, MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem specialization_X_succ (i : Fin 3) :
    specialization k (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [specialization, MvPolynomial.finSuccEquiv_X_succ]

@[simp] theorem specialization_C (a : k) :
    specialization k (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [specialization, MvPolynomial.finSuccEquiv_apply]

def tailInclusion : Poly k 3 →ₐ[k] Poly k 4 := MvPolynomial.rename Fin.succ

@[simp] theorem specialization_tailInclusion (f : Poly k 3) :
    specialization k (tailInclusion k f) = f := by
  have h : (specialization k).comp (tailInclusion k).toRingHom = RingHom.id _ := by
    ext i <;> simp [tailInclusion]
  exact RingHom.congr_fun h f

theorem specialization_surjective : Function.Surjective (specialization k) :=
  fun f => ⟨tailInclusion k f, specialization_tailInclusion k f⟩

theorem ker_specialization :
    RingHom.ker (specialization k) = Ideal.span {MvPolynomial.X (0 : Fin 4)} := by
  ext f
  change Polynomial.constantCoeff (MvPolynomial.finSuccEquiv k 3 f) = 0 ↔ _
  rw [Polynomial.constantCoeff_apply, ← Polynomial.X_dvd_iff,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(MvPolynomial.finSuccEquiv k 3).symm g, ?_⟩
    apply (MvPolynomial.finSuccEquiv k 3).injective
    simpa [MvPolynomial.finSuccEquiv_X_zero] using hg
  · rintro ⟨g, rfl⟩
    exact ⟨MvPolynomial.finSuccEquiv k 3 g, by simp [MvPolynomial.finSuccEquiv_X_zero]⟩

def specializationQuotientEquiv :
    (Poly k 4 ⧸ RingHom.ker (specialization k)) ≃+* Poly k 3 :=
  RingHom.quotientKerEquivOfSurjective (specialization_surjective k)

def JGamma (H : AddSubmonoid ℕ) (w : Fin 4 → H) : Ideal (Poly k 3) :=
  Ideal.map (specialization k) (toricIdeal k H w)

/-- This comap identity identifies J exactly with (I + (x0))/(x0). -/
theorem comap_JGamma (H : AddSubmonoid ℕ) (w : Fin 4 → H) :
    Ideal.comap (specialization k) (JGamma k H w) =
      toricIdeal k H w ⊔ Ideal.span {MvPolynomial.X (0 : Fin 4)} := by
  rw [JGamma, Ideal.comap_map_of_surjective _ (specialization_surjective k),
    ← RingHom.ker_eq_comap_bot, ker_specialization]

/-- The easy direction of MUJ; equality is a separate graded-algebra obligation. -/
theorem JGamma_generatorNumber_le (H : AddSubmonoid ℕ) (w : Fin 4 → H) :
    (JGamma k H w).spanFinrank ≤ toricGeneratorNumber k H w :=
  Ideal.spanFinrank_map_le_of_fg (specialization k) (toricIdeal_fg k H w)

theorem toricMap_tailInclusion (H : AddSubmonoid ℕ) (w : Fin 4 → H) (f : Poly k 3) :
    toricMap k H w (tailInclusion k f) = toricMap k H (fun i => w i.succ) f := by
  have h : (toricMap k H w).comp (tailInclusion k) =
      toricMap k H (fun i => w i.succ) := by
    ext i
    simp [tailInclusion]
  exact DFunLike.congr_fun h f

/-- Tail relations are included in the specialized four-variable toric ideal. -/
theorem tailToricIdeal_le_JGamma (H : AddSubmonoid ℕ) (w : Fin 4 → H) :
    toricIdeal k H (fun i => w i.succ) ≤ JGamma k H w := by
  intro f hf
  rw [← specialization_tailInclusion k f]
  apply Ideal.mem_map_of_mem
  change toricMap k H w (tailInclusion k f) = 0
  rw [toricMap_tailInclusion]
  exact hf

/-- Pulling the principal monomial ideal back along the full toric quotient. -/
theorem comap_principal_toricMap (H : AddSubmonoid ℕ) (w : Fin 4 → H)
    (hgen : AddSubmonoid.closure (Set.range w) = ⊤) :
    Ideal.comap (toricMap k H w).toRingHom
        (Ideal.span {AddMonoidAlgebra.single (w 0) (1 : k)}) =
      toricIdeal k H w ⊔ Ideal.span {MvPolynomial.X (0 : Fin 4)} := by
  rw [← toricMap_X k H w 0, ← Set.image_singleton, ← Ideal.map_span]
  change Ideal.comap (toricMap k H w).toRingHom
    (Ideal.map (toricMap k H w).toRingHom _) = _
  rw [Ideal.comap_map_of_surjective (toricMap k H w).toRingHom
    (toricMap_surjective k H w hgen)]
  change _ ⊔ toricIdeal k H w = _
  exact sup_comm _ _

/-- Exact elimination description of J, before the monomial generator dictionary. -/
theorem JGamma_eq_comap_principal (H : AddSubmonoid ℕ) (w : Fin 4 → H)
    (hgen : AddSubmonoid.closure (Set.range w) = ⊤) :
    JGamma k H w = Ideal.comap (toricMap k H (fun i => w i.succ)).toRingHom
      (Ideal.span {AddMonoidAlgebra.single (w 0) (1 : k)}) := by
  ext f
  have h := congrArg (fun I : Ideal (Poly k 4) => tailInclusion k f ∈ I)
    (comap_JGamma k H w)
  rw [← comap_principal_toricMap k H w hgen] at h
  change (specialization k (tailInclusion k f) ∈ JGamma k H w) =
    (toricMap k H w (tailInclusion k f) ∈
      Ideal.span {AddMonoidAlgebra.single (w 0) (1 : k)}) at h
  rw [specialization_tailInclusion, toricMap_tailInclusion] at h
  exact iff_of_eq h

end NS25Lean.ToricPresentation
