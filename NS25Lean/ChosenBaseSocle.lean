import NS25Lean.ChosenBaseBasis

set_option linter.style.header false

noncomputable section
namespace NS25Lean.ChosenBase
open ToricPresentation FourGeneratedBridge
variable (k : Type*) [Field k] {Gamma : NumericalSemigroup}

/-- The annihilator of all positive-degree monomials in the Artinian quotient. -/
def Data.socleA (B : Data Gamma) : Submodule k (B.A k) where
  carrier := {x | ∀ h : Gamma.toAddSubmonoid, h ≠ 0 → B.monomialClass k h * x = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy h hh; rw [mul_add, hx h hh, hy h hh, add_zero]
  smul_mem' := by intro a x hx h hh; rw [mul_smul_comm, hx h hh, smul_zero]

theorem Data.monomialClass_mul (B : Data Gamma) (h g : Gamma.toAddSubmonoid) :
    B.monomialClass k h * B.monomialClass k g = B.monomialClass k (h + g) := by
  simp [Data.monomialClass, ← map_mul, AddMonoidAlgebra.single_mul_single]

def Data.socleToApery (B : Data Gamma)
    (w : {w // IsSocle Gamma.toAddSubmonoid B.H B.q.val w}) : B.apery :=
  ⟨w.val, B.apery_eq_compl.symm ▸ ⟨w.property.1, w.property.2.1⟩⟩

theorem Data.socleToApery_injective (B : Data Gamma) : Function.Injective B.socleToApery := by
  intro a b he
  exact Subtype.ext (congrArg (fun w : B.apery => w.val) he)

def Data.socleClass (B : Data Gamma)
    (w : {w // IsSocle Gamma.toAddSubmonoid B.H B.q.val w}) : B.A k :=
  B.monomialClass k (B.aperyDegree (B.socleToApery w))

theorem Data.socleClass_mem (B : Data Gamma)
    (w : {w // IsSocle Gamma.toAddSubmonoid B.H B.q.val w}) :
    B.socleClass k w ∈ B.socleA k := by
  intro h hh
  change B.monomialClass k h * B.monomialClass k (B.aperyDegree (B.socleToApery w)) = 0
  rw [B.monomialClass_mul k, B.monomialClass_eq_zero_iff k]
  have hpf := (isSocle_iff_isPseudoFrobeniusInt B.q_positive B.q.property B.H_le
    B.generatedOver).mp w.property
  have hn : h.val ≠ 0 := fun he => hh (Subtype.ext he)
  obtain ⟨a, ha, he⟩ := hpf.2 h.val h.property hn
  rintro ⟨_, hlt | hnot⟩
  · change h.val + w.val < B.q.val at hlt
    omega
  · apply hnot
    have he' : h.val + w.val - B.q.val = a := by omega
    change h.val + w.val - B.q.val ∈ Gamma.toAddSubmonoid
    rw [he']
    exact ha

/-- Nonzero surviving coefficients of a socle element have maximal Apéry degree.
Translation by a monomial is injective on exponents, so no cancellation is hidden. -/
theorem Data.socle_support (B : Data Gamma) (f : SemigroupAlgebra k Gamma.toAddSubmonoid)
    (hf : B.quotientMap k f ∈ B.socleA k) (w : B.apery)
    (hw : f.coeff (B.aperyDegree w) ≠ 0) :
    IsSocle Gamma.toAddSubmonoid B.H B.q.val w.val := by
  have hwa : w.val ∈ B.H ∧ w.val ∉ B.K := by
    exact Eq.mp (congrArg (fun s : Set ℕ => w.val ∈ s) B.apery_eq_compl) w.property
  refine ⟨hwa.1, hwa.2, ?_⟩
  intro h hh hn
  let g : Gamma.toAddSubmonoid := ⟨h, B.H_le hh⟩
  have hgn : g ≠ 0 := fun he => hn (congrArg (fun x : Gamma.toAddSubmonoid => x.val) he)
  have hp : AddMonoidAlgebra.single g 1 * f ∈ B.principal k := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change B.quotientMap k (AddMonoidAlgebra.single g 1 * f) = 0
    rw [map_mul]
    exact hf g hgn
  have hc : (AddMonoidAlgebra.single g 1 * f).coeff (g + B.aperyDegree w) ≠ 0 := by
    simpa only [AddMonoidAlgebra.coeff_single_mul_add, one_mul] using hw
  have hm := (mem_principal_monomial_iff k _ B.q _).mp hp _ (Finsupp.mem_support_iff.mpr hc)
  refine ⟨B.H.add_mem hwa.1 hh, ?_, ?_⟩
  · have hmle : B.q.val ≤ h + w.val := hm.1
    omega
  · have he : w.val + h - B.q.val = (g + B.aperyDegree w).val - B.q.val := by
      change w.val + h - B.q.val = h + w.val - B.q.val
      omega
    rw [he]
    exact hm.2

theorem Data.socleClass_linearIndependent (B : Data Gamma) :
    LinearIndependent k (B.socleClass k) :=
  (B.apery_linearIndependent k).comp B.socleToApery B.socleToApery_injective

theorem Data.quotient_expansion (B : Data Gamma) (f : SemigroupAlgebra k Gamma.toAddSubmonoid) :
    B.quotientMap k f = ∑ h ∈ f.coeff.support, f.coeff h • B.monomialClass k h := by
  calc
    B.quotientMap k f = B.quotientMap k (f.coeff.sum AddMonoidAlgebra.single) := by
      rw [AddMonoidAlgebra.sum_coeff_single]
    _ = _ := by simp [Finsupp.sum, Data.monomialClass, ← map_smul]

/-- The entire algebraic socle, not merely its monomial elements, has this span. -/
theorem Data.socle_eq_span (B : Data Gamma) :
    B.socleA k = Submodule.span k (Set.range (B.socleClass k)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    change B.quotientMap k f ∈ _
    rw [B.quotient_expansion k]
    apply Submodule.sum_mem
    intro h hh
    apply Submodule.smul_mem
    by_cases ha : h.val ∈ B.apery
    · have hw := B.socle_support k f hx ⟨h.val, ha⟩ (Finsupp.mem_support_iff.mp hh)
      exact Submodule.subset_span ⟨⟨h.val, hw⟩, rfl⟩
    · rw [(B.monomialClass_eq_zero_iff k h).mpr ha]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact B.socleClass_mem k w

def Data.socleBasis (B : Data Gamma) :
    Module.Basis {w // IsSocle Gamma.toAddSubmonoid B.H B.q.val w} k (B.socleA k) :=
  (Module.Basis.span (B.socleClass_linearIndependent k)).map
    (LinearEquiv.ofEq _ _ (B.socle_eq_span k).symm)

/-- A6 in A_q: actual socle dimension, linked to the frozen PF correspondence. -/
theorem Data.socle_finrank_eq_type (B : Data Gamma) :
    Module.finrank k (B.socleA k) = Gamma.asRelativeIdeal.idealType := by
  rw [Module.finrank_eq_nat_card_basis (B.socleBasis k)]
  exact (natCard_socle_eq_pseudoFrobeniusInt B.q_positive B.q.property B.H_le
    B.generatedOver).trans (natCard_pseudoFrobeniusInt_eq_idealType Gamma)

/-- Transport of the positive-degree annihilator across the actual algebra equivalence. -/
def Data.soclePolynomialQuotient (B : Data Gamma) :
    Submodule k (MvPolynomial (Fin 3) k ⧸ B.J k) :=
  (B.socleA k).comap (B.quotientEquiv k).toLinearMap

def Data.socleQuotientEquiv (B : Data Gamma) :
    B.soclePolynomialQuotient k ≃ₗ[k] B.socleA k :=
  (B.quotientEquiv k).toLinearEquiv.ofSubmodule' (B.socleA k)

/-- The quotient type is the dimension of its actual transported socle. -/
def Data.quotientType (B : Data Gamma) : ℕ :=
  Module.finrank k (B.soclePolynomialQuotient k)

theorem Data.quotient_type_eq (B : Data Gamma) :
    B.quotientType k = Gamma.asRelativeIdeal.idealType :=
  (B.socleQuotientEquiv k).finrank_eq.trans (B.socle_finrank_eq_type k)

end NS25Lean.ChosenBase
