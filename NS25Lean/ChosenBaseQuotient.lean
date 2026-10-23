import NS25Lean.ChosenBaseMUJ

set_option linter.style.header false

noncomputable section
namespace NS25Lean.ChosenBase
open MvPolynomial ToricPresentation Presentation FourGeneratedBridge
variable (k : Type*) [Field k] {Gamma : NumericalSemigroup}

def Data.principal (B : Data Gamma) : Ideal (SemigroupAlgebra k Gamma.toAddSubmonoid) :=
  Ideal.span {AddMonoidAlgebra.single B.q (1 : k)}

abbrev Data.A (B : Data Gamma) := SemigroupAlgebra k Gamma.toAddSubmonoid ⧸ B.principal k

def Data.quotientMap (B : Data Gamma) : SemigroupAlgebra k Gamma.toAddSubmonoid →ₐ[k] B.A k :=
  Ideal.Quotient.mkₐ k (B.principal k)

def Data.psi (B : Data Gamma) : Poly k 3 →ₐ[k] B.A k :=
  (B.quotientMap k).comp (toricMap k Gamma.toAddSubmonoid (fun j => B.degrees j.succ))

def Data.J (B : Data Gamma) : Ideal (Poly k 3) := RingHom.ker (B.psi k).toRingHom

def Data.IH (B : Data Gamma) : Ideal (Poly k 3) := toricIdeal k B.H B.tailDegrees

/-- Boundary monomial ideal in the three-variable polynomial ring, distinct from K
and from the monomial ideal in the semigroup algebra k[H]. -/
def Data.MK (B : Data Gamma) : Ideal (Poly k 3) :=
  Ideal.span ((fun u : Fin 3 →₀ ℕ => monomial u (1 : k)) ''
    {u | (factorizationMap B.tailDegrees u).val ∈ B.K})

theorem Data.J_eq_specialized (B : Data Gamma) :
    B.J k = JGamma k Gamma.toAddSubmonoid B.degrees := by
  rw [JGamma_eq_comap_principal k _ _ B.degrees_generate]
  ext f
  change B.quotientMap k (toricMap k _ _ f) = 0 ↔ _
  rw [show B.quotientMap k = Ideal.Quotient.mkₐ k (B.principal k) from rfl]
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  simp only [Ideal.mem_comap, B.degrees_zero]
  rfl

theorem Data.psi_specialization (B : Data Gamma) (f : Poly k 4) :
    B.psi k (specialization k f) = B.quotientMap k (toricMap k _ B.degrees f) := by
  have he : (B.psi k).toRingHom.comp (specialization k) =
      (B.quotientMap k).toRingHom.comp (toricMap k _ B.degrees).toRingHom := by
    ext i : 1
    · ext a
      change B.psi k (specialization k (C a)) = B.quotientMap k (toricMap k _ _ (C a))
      rw [specialization_C]
      change B.psi k (algebraMap k (Poly k 3) a) =
        B.quotientMap k (toricMap k _ B.degrees (algebraMap k (Poly k 4) a))
      simp only [AlgHom.commutes]
    · refine Fin.cases ?_ (fun j => ?_) i
      · change B.psi k (specialization k (X 0)) = B.quotientMap k (toricMap k _ _ (X 0))
        simp only [specialization_X_zero, map_zero, toricMap_X, B.degrees_zero]
        symm
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact Ideal.subset_span (Set.mem_singleton _)
      · simp [Data.psi]
  exact RingHom.congr_fun he f

theorem Data.psi_surjective (B : Data Gamma) : Function.Surjective (B.psi k) := by
  intro a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨p, rfl⟩ := toricMap_surjective k _ B.degrees B.degrees_generate f
  exact ⟨specialization k p, B.psi_specialization k p⟩

/-- A2: the actual tail kernel gives the source's algebra quotient correspondence. -/
def Data.quotientEquiv (B : Data Gamma) : (Poly k 3 ⧸ B.J k) ≃ₐ[k] B.A k :=
  Ideal.quotientKerAlgEquivOfSurjective (B.psi_surjective k)

/-- Exact MUJ for J defined as the actual kernel of the tail-to-Apéry-quotient map. -/
theorem Data.muj (B : Data Gamma) : (B.J k).spanFinrank = Presentation.rho Gamma := by
  rw [B.J_eq_specialized k]
  exact B.specialized_muj k

theorem Data.tailMap_monomial (B : Data Gamma) (u : Fin 3 →₀ ℕ) :
    toricMap k B.H B.tailDegrees (monomial u 1) =
      AddMonoidAlgebra.single (factorizationMap B.tailDegrees u) 1 := by
  rw [← factorizationAlgebraMap_eq_toricMap]
  change AddMonoidAlgebra.mapDomainAlgHom k k (factorizationMap B.tailDegrees)
    (AddMonoidAlgebra.single u 1) = _
  simp

theorem Data.map_MK (B : Data Gamma) :
    Ideal.map (toricMap k B.H B.tailDegrees).toRingHom (B.MK k) =
      tailMonomialIdeal k Gamma.toAddSubmonoid B.H B.q.val := by
  rw [Data.MK, Ideal.map_span, tailMonomialIdeal]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨factorizationMap B.tailDegrees u, hu, ?_⟩
    exact (B.tailMap_monomial k u).symm
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨u, hu⟩ := factorizationMap_surjective B.tailDegrees B.tailDegrees_generate h
    refine ⟨monomial u 1, ⟨u, ?_, rfl⟩, ?_⟩
    · change (factorizationMap B.tailDegrees u).val ∈ B.K
      rw [hu]
      exact hh
    · change toricMap k B.H B.tailDegrees (monomial u 1) = AddMonoidAlgebra.single h 1
      rw [B.tailMap_monomial k, hu]

theorem Data.J_eq_comap_tail (B : Data Gamma) :
    B.J k = Ideal.comap (toricMap k B.H B.tailDegrees).toRingHom
      (tailMonomialIdeal k Gamma.toAddSubmonoid B.H B.q.val) := by
  rw [B.J_eq_specialized k]
  simpa only [B.degrees_zero] using JGamma_eq_comap_tailMonomialIdeal k _ _ B.H_le
    B.degrees B.tailDegrees (fun _ => rfl) B.degrees_generate

/-- A5: both inclusions, with the tail toric and polynomial monomial ideals separated. -/
theorem Data.J_eq_IH_sup_MK (B : Data Gamma) : B.J k = B.IH k ⊔ B.MK k := by
  rw [B.J_eq_comap_tail k, ← B.map_MK k,
    Ideal.comap_map_of_surjective (toricMap k B.H B.tailDegrees).toRingHom
      (toricMap_surjective k _ _ B.tailDegrees_generate)]
  change B.MK k ⊔ B.IH k = B.IH k ⊔ B.MK k
  exact sup_comm _ _

end NS25Lean.ChosenBase
