import NS25Lean.DilationIdeals

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase ToricPresentation FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

theorem dilatedData_mem_H (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) (n : ℕ) :
    n ∈ (dilatedData B D hD hcop).H ↔ ∃ h ∈ B.H, n = D * h := by
  rw [dilatedData_H]
  change (∃ h ∈ B.H, D * h = n) ↔ _
  exact ⟨fun ⟨h, hh, he⟩ => ⟨h, hh, he.symm⟩,
    fun ⟨h, hh, he⟩ => ⟨h, hh, he.symm⟩⟩

theorem dilation_source_iff (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) (x : ℕ) :
    IsMinimalTailGenerator (dilatedData B D hD hcop).H
      (dilatedData B D hD hcop).K (D * x) ↔ IsMinimalTailGenerator B.H B.K x := by
  have hDpos := lt_trans B.q_positive hD
  constructor
  · rintro ⟨hx, hm⟩
    refine ⟨(dilatedData_K B D hD hcop x).mp hx, ?_⟩
    intro h hh hn
    have hn' : D * h ≠ 0 := mul_ne_zero (ne_of_gt hDpos) hn
    rcases hm (D * h) ((dilatedData_mem_H B D hD hcop _).mpr ⟨h, hh, rfl⟩) hn' with
      he | he
    · exact Or.inl ((Nat.mul_lt_mul_left hDpos).mp he)
    · right
      intro hc
      apply he
      rw [← Nat.mul_sub_left_distrib]
      exact (dilatedData_K B D hD hcop _).mpr hc
  · rintro ⟨hx, hm⟩
    refine ⟨(dilatedData_K B D hD hcop x).mpr hx, ?_⟩
    intro n hn hnz
    obtain ⟨h, hh, rfl⟩ := (dilatedData_mem_H B D hD hcop n).mp hn
    have hn' : h ≠ 0 := by intro he; simp [he] at hnz
    rcases hm h hh hn' with he | he
    · exact Or.inl ((Nat.mul_lt_mul_left hDpos).mpr he)
    · right
      rw [← Nat.mul_sub_left_distrib, dilatedData_K]
      exact he

def dilationSourceEquiv (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) :
    {x // IsMinimalTailGenerator B.H B.K x} ≃
      {x // IsMinimalTailGenerator (dilatedData B D hD hcop).H
        (dilatedData B D hD hcop).K x} :=
  Equiv.ofBijective (fun x => ⟨D * x.val, (dilation_source_iff B D hD hcop x.val).mpr x.property⟩)
    ⟨by
      intro x y he
      apply Subtype.ext
      exact Nat.eq_of_mul_eq_mul_left (lt_trans B.q_positive hD) (congrArg Subtype.val he), by
      intro x
      obtain ⟨h, hh, he⟩ := (dilatedData_mem_H B D hD hcop x.val).mp x.property.1.1
      refine ⟨⟨h, (dilation_source_iff B D hD hcop h).mp (he ▸ x.property)⟩, ?_⟩
      exact Subtype.ext he.symm⟩

theorem dilation_sourceCount (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) :
    sourceCount (dilatedData B D hD hcop) = sourceCount B :=
  (Nat.card_congr (dilationSourceEquiv B D hD hcop)).symm

theorem dilation_defect (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) :
    chosenDefect (dilatedData B D hD hcop) = chosenDefect B := by
  unfold chosenDefect
  rw [dilation_rho B D hD hcop, dilation_sourceCount]

theorem dilation_socle_mem_iff (k : Type*) [Field k] (B : Data Gamma) (D : ℕ)
    (hD : B.q.val < D) (hcop : Nat.Coprime D B.q.val)
    (x : Poly k 3 ⧸ (dilatedData B D hD hcop).J k) :
    dilationQuotientEquiv k B D hD hcop x ∈ B.soclePolynomialQuotient k ↔
      x ∈ (dilatedData B D hD hcop).soclePolynomialQuotient k := by
  rw [Data.soclePolynomialQuotient_iff_variables, Data.soclePolynomialQuotient_iff_variables]
  constructor
  · intro hx j
    apply (dilationQuotientEquiv k B D hD hcop).injective
    simpa only [map_mul, map_zero, dilationQuotientEquiv_mk] using hx j
  · intro hx j
    have he := congrArg (dilationQuotientEquiv k B D hD hcop) (hx j)
    simpa only [map_mul, map_zero, dilationQuotientEquiv_mk] using he

def dilationSocleEquiv (k : Type*) [Field k] (B : Data Gamma) (D : ℕ)
    (hD : B.q.val < D) (hcop : Nat.Coprime D B.q.val) :
    (dilatedData B D hD hcop).soclePolynomialQuotient k ≃ₗ[k] B.soclePolynomialQuotient k :=
  (dilationQuotientEquiv k B D hD hcop).toLinearEquiv.ofSubmodules _ _ (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (dilation_socle_mem_iff k B D hD hcop x).mpr hx
    · intro hy
      refine ⟨(dilationQuotientEquiv k B D hD hcop).symm y, ?_, by simp⟩
      apply (dilation_socle_mem_iff k B D hD hcop _).mp
      simpa using hy)

theorem dilation_type (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) :
    (dilatedSemigroup B D hcop).asRelativeIdeal.idealType = Gamma.asRelativeIdeal.idealType := by
  rw [← (dilatedData B D hD hcop).quotient_type_eq ℚ, ← B.quotient_type_eq ℚ]
  exact (dilationSocleEquiv ℚ B D hD hcop).finrank_eq

/-- Usable change-of-base transfer, retaining the original arbitrary chosen pivot. -/
theorem dilation_transfer (B : Data Gamma) (D : ℕ) (hD : B.q.val < D)
    (hcop : Nat.Coprime D B.q.val) :
    IsMultiplicity (dilatedData B D hD hcop) ∧
    Presentation.rho (dilatedSemigroup B D hcop) = Presentation.rho Gamma ∧
    (dilatedSemigroup B D hcop).asRelativeIdeal.idealType = Gamma.asRelativeIdeal.idealType ∧
    sourceCount (dilatedData B D hD hcop) = sourceCount B ∧
    chosenDefect (dilatedData B D hD hcop) = chosenDefect B :=
  ⟨dilatedData_isMultiplicity B D hD hcop, dilation_rho B D hD hcop,
    dilation_type B D hD hcop, dilation_sourceCount B D hD hcop, dilation_defect B D hD hcop⟩

end NS25Lean.L2B
