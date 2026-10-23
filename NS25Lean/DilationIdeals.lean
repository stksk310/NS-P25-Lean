import NS25Lean.DilationMinimality

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase ToricPresentation Presentation MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem dilatedData_H (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) :
    (dilatedData B D hD hcop).H = dilatedTail B D := by
  change AddSubmonoid.closure (Set.range (weights (dilatedData B D hD hcop))) =
    (AddSubmonoid.closure (Set.range (weights B))).map (scaleHom D)
  apply le_antisymm
  · apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨weights B j, AddSubmonoid.subset_closure ⟨j, rfl⟩,
      (dilatedData_weights B D hD hcop j).symm⟩
  · rintro n ⟨h, hh, rfl⟩
    induction hh using AddSubmonoid.closure_induction with
    | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact AddSubmonoid.subset_closure ⟨j, dilatedData_weights B D hD hcop j⟩
    | zero => simpa using (dilatedData B D hD hcop).H.zero_mem
    | add a b ha hb iha ihb =>
        rw [map_add]
        exact (AddSubmonoid.closure (Set.range
          (weights (dilatedData B D hD hcop)))).add_mem iha ihb

theorem dilatedData_weight (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) (u : Fin 3 →₀ ℕ) :
    weight (dilatedData B D hD hcop) u = D * weight B u := by
  simp only [weight_eq_sum, dilatedData_weights, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem dilatedData_K (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) (h : ℕ) :
    D * h ∈ (dilatedData B D hD hcop).K ↔ h ∈ B.K := by
  unfold Data.K
  rw [dilatedData_H, dilatedData_q]
  exact dilation_K_iff B D (lt_trans B.q_positive hD) hcop h

theorem IH_eq_relationIdeal (k : Type*) [Field k] (B : Data Gamma) :
    B.IH k = relationIdeal k {p | weight B p.1 = weight B p.2} := by
  rw [Data.IH, toricIdeal, ← factorizationAlgebraMap_eq_toricMap,
    ← relationIdeal_factorization_eq_ker]
  congr 1
  ext p
  change factorizationMap B.tailDegrees p.1 = factorizationMap B.tailDegrees p.2 ↔ _
  rw [← Subtype.val_inj, ← weight_eq_degree, ← weight_eq_degree]
  rfl

theorem dilatedData_IH (k : Type*) [Field k] (B : Data Gamma) (D : ℕ)
    (hD : B.q.val < D) (hcop : Nat.Coprime D B.q.val) :
    (dilatedData B D hD hcop).IH k = B.IH k := by
  rw [IH_eq_relationIdeal, IH_eq_relationIdeal]
  congr 1
  ext p
  simp only [Set.mem_setOf_eq, dilatedData_weight]
  exact Nat.mul_right_inj (ne_of_gt (lt_trans B.q_positive hD))

theorem dilatedData_MK (k : Type*) [Field k] (B : Data Gamma) (D : ℕ)
    (hD : B.q.val < D) (hcop : Nat.Coprime D B.q.val) :
    (dilatedData B D hD hcop).MK k = B.MK k := by
  unfold Data.MK
  congr 2
  ext u
  simp only [Set.mem_setOf_eq, ← weight_eq_degree, dilatedData_weight, dilatedData_K]

theorem dilatedData_J (k : Type*) [Field k] (B : Data Gamma) (D : ℕ)
    (hD : B.q.val < D) (hcop : Nat.Coprime D B.q.val) :
    (dilatedData B D hD hcop).J k = B.J k := by
  rw [Data.J_eq_IH_sup_MK, Data.J_eq_IH_sup_MK, dilatedData_IH, dilatedData_MK]

def dilationQuotientEquiv (k : Type*) [Field k] (B : Data Gamma) (D : ℕ)
    (hD : B.q.val < D) (hcop : Nat.Coprime D B.q.val) :
    (Poly k 3 ⧸ (dilatedData B D hD hcop).J k) ≃ₐ[k] (Poly k 3 ⧸ B.J k) :=
  Ideal.quotientEquivAlgOfEq k (dilatedData_J k B D hD hcop)

@[simp] theorem dilationQuotientEquiv_mk (k : Type*) [Field k] (B : Data Gamma) (D : ℕ)
    (hD : B.q.val < D) (hcop : Nat.Coprime D B.q.val) (f : Poly k 3) :
    dilationQuotientEquiv k B D hD hcop
      (Ideal.Quotient.mk ((dilatedData B D hD hcop).J k) f) =
      Ideal.Quotient.mk (B.J k) f := Ideal.quotientEquivAlgOfEq_mk k _ f

theorem dilation_rho (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) :
    rho (dilatedSemigroup B D hcop) = rho Gamma := by
  rw [← (dilatedData B D hD hcop).muj ℚ, dilatedData_J ℚ B D hD hcop, B.muj ℚ]

end NS25Lean.L2B
