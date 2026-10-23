import NS25Lean.GcdNormalization

set_option linter.style.header false

namespace NS25Lean.FourGeneratedBridge

/-- Internal scaling interface, constructed from the four generators below. -/
structure TailScaling (Gamma H : AddSubmonoid ℕ) (m : ℕ) where
  Hbar : NumericalSemigroup
  d : ℕ
  positive : 0 < d
  scale : ∀ x, x ∈ H ↔ ∃ y ∈ Hbar, x = d * y
  inclusion : H ≤ Gamma
  nonempty : (aperyTail Gamma H m).Nonempty

namespace TailScaling
variable {Gamma H : AddSubmonoid ℕ} {m : ℕ} (S : TailScaling Gamma H m)

theorem mul_mem_iff (x : ℕ) : S.d * x ∈ H ↔ x ∈ S.Hbar := by
  rw [S.scale]
  constructor
  · rintro ⟨y, hy, heq⟩
    have : x = y := Nat.eq_of_mul_eq_mul_left S.positive heq
    simpa [this] using hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

theorem dvd_of_mem {x : ℕ} (hx : x ∈ H) : S.d ∣ x := by
  obtain ⟨y, hy, heq⟩ := (S.scale x).mp hx
  exact ⟨y, heq⟩

theorem div_mem {x : ℕ} (hx : x ∈ H) : x / S.d ∈ S.Hbar := by
  obtain ⟨y, hy, heq⟩ := (S.scale x).mp hx
  simpa [heq, Nat.mul_div_cancel_left _ S.positive] using hy

/-- Division by `d` is an additive equivalence, with inverse multiplication. -/
def monoidEquiv : H ≃+ S.Hbar.toAddSubmonoid where
  toFun x := ⟨x.val / S.d, S.div_mem x.property⟩
  invFun y := ⟨S.d * y.val, (S.mul_mem_iff y.val).mpr y.property⟩
  left_inv x := Subtype.ext (Nat.mul_div_cancel' (S.dvd_of_mem x.property))
  right_inv y := Subtype.ext (Nat.mul_div_cancel_left y.val S.positive)
  map_add' x y := by
    apply Subtype.ext
    change (x.val + y.val) / S.d = x.val / S.d + y.val / S.d
    apply Nat.eq_of_mul_eq_mul_left S.positive
    rw [Nat.mul_add, Nat.mul_div_cancel' (dvd_add (S.dvd_of_mem x.property)
      (S.dvd_of_mem y.property)), Nat.mul_div_cancel' (S.dvd_of_mem x.property),
      Nat.mul_div_cancel' (S.dvd_of_mem y.property)]

/-- `K/d`, embedded in `ℤ`. Nonnegativity here follows from the actual tail,
and does not restrict the general relative-ideal API. -/
def ideal : RelativeIdeal S.Hbar where
  carrier := {z | ∃ x : ℕ, S.d * x ∈ aperyTail Gamma H m ∧ z = x}
  nonempty := by
    obtain ⟨w, hw⟩ := S.nonempty
    obtain ⟨x, hx, heq⟩ := (S.scale w).mp hw.1
    exact ⟨x, x, by simpa [← heq] using hw, rfl⟩
  bddBelow := ⟨0, by rintro z ⟨x, hx, rfl⟩; exact Int.natCast_nonneg x⟩
  add_mem := by
    rintro z h ⟨x, hx, rfl⟩ hh
    refine ⟨x + h, ?_, by simp⟩
    simpa [Nat.mul_add] using aperyTail_add_mem S.inclusion hx ((S.mul_mem_iff h).mpr hh)

@[simp] theorem mem_ideal_nat (x : ℕ) :
    (x : ℤ) ∈ S.ideal ↔ S.d * x ∈ aperyTail Gamma H m := by
  constructor
  · rintro ⟨y, hy, heq⟩
    have : x = y := by exact_mod_cast heq
    simpa [this] using hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

theorem ideal_nonneg {z : ℤ} (hz : z ∈ S.ideal) : 0 ≤ z := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact Int.natCast_nonneg x

/-- Exact integer preimage description; negative integers have not been
silently truncated by natural-number subtraction. -/
theorem mem_ideal_iff (z : ℤ) : z ∈ S.ideal ↔
    ∃ w : ℕ, w ∈ aperyTail Gamma H m ∧ (S.d : ℤ) * z = w := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨S.d * x, hx, by simp⟩
  · rintro ⟨w, hw, heq⟩
    obtain ⟨x, hx, hwx⟩ := (S.scale w).mp hw.1
    have hd : (0 : ℤ) < S.d := by exact_mod_cast S.positive
    have heq' : (S.d : ℤ) * z = S.d * (x : ℤ) := by simpa [hwx] using heq
    have hz : z = (x : ℤ) := mul_left_cancel₀ (ne_of_gt hd) heq'
    exact ⟨x, by simpa [← hwx] using hw, hz⟩

theorem socle_iff (x : ℕ) : IsSocle Gamma H m (S.d * x) ↔
    IsIntegralSocle S.ideal (x : ℤ) := by
  constructor
  · rintro ⟨hxH, hxnot, hxadd⟩
    refine ⟨⟨x, (S.mul_mem_iff x).mp hxH, rfl⟩, ?_, ?_⟩
    · exact fun hx ↦ hxnot ((S.mem_ideal_nat x).mp hx)
    · intro h hh hn
      have hdn : S.d * h ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt S.positive) hn
      have ht := hxadd (S.d * h) ((S.mul_mem_iff h).mpr hh) hdn
      have ht' : ((x + h : ℕ) : ℤ) ∈ S.ideal :=
        (S.mem_ideal_nat (x + h)).mpr (by simpa [Nat.mul_add] using ht)
      simpa using ht'
  · rintro ⟨⟨y, hy, heq⟩, hxnot, hxadd⟩
    have hxy : x = y := by exact_mod_cast heq
    have hxH := (S.mul_mem_iff x).mpr (by simpa [hxy] using hy)
    refine ⟨hxH, fun hx ↦ hxnot ((S.mem_ideal_nat x).mpr hx), ?_⟩
    intro h hh hn
    obtain ⟨y, hy, rfl⟩ := (S.scale h).mp hh
    have hyn : y ≠ 0 := by intro hz; simp [hz] at hn
    have ht := hxadd y hy hyn
    have ht' := (S.mem_ideal_nat (x + y)).mp (by simpa using ht)
    simpa [Nat.mul_add] using ht'

theorem generator_iff (x : ℕ) :
    IsMinimalTailGenerator H (aperyTail Gamma H m) (S.d * x) ↔
      S.ideal.IsMinimalGenerator (x : ℤ) := by
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨(S.mem_ideal_nat x).mpr hx, ?_⟩
    intro h hh hn hbad
    have hxhle : h ≤ x := by have := S.ideal_nonneg hbad; omega
    have hbad' : ((x - h : ℕ) : ℤ) ∈ S.ideal := by
      simpa [Nat.cast_sub hxhle] using hbad
    have ht := (S.mem_ideal_nat (x - h)).mp hbad'
    rcases hmin (S.d * h) ((S.mul_mem_iff h).mpr hh)
      (Nat.mul_ne_zero (Nat.ne_of_gt S.positive) hn) with hlt | hnot
    · have := Nat.mul_le_mul_left S.d hxhle
      omega
    · exact hnot (by simpa [Nat.mul_sub] using ht)
  · rintro ⟨hx, hmin⟩
    refine ⟨(S.mem_ideal_nat x).mp hx, ?_⟩
    intro h hh hn
    obtain ⟨y, hy, rfl⟩ := (S.scale h).mp hh
    have hyn : y ≠ 0 := by intro hz; simp [hz] at hn
    by_cases hxy : x < y
    · exact Or.inl (Nat.mul_lt_mul_of_pos_left hxy S.positive)
    · right
      intro hbad
      have hyx : y ≤ x := by omega
      have ht : ((x - y : ℕ) : ℤ) ∈ S.ideal :=
        (S.mem_ideal_nat (x - y)).mpr (by simpa [Nat.mul_sub] using hbad)
      exact hmin y hy hyn (by simpa [Nat.cast_sub hyx] using ht)

/-- Forward division and inverse multiplication for the socle. -/
noncomputable def socleEquiv :
    {w // IsSocle Gamma H m w} ≃ {z // IsIntegralSocle S.ideal z} := by
  let F : {z // IsIntegralSocle S.ideal z} → {w // IsSocle Gamma H m w} := fun z ↦
    ⟨S.d * z.val.toNat, (S.socle_iff z.val.toNat).mpr (by
      obtain ⟨x, hx, heq⟩ := z.property.1
      simpa [heq] using z.property)⟩
  have hinj : Function.Injective F := by
    intro z v heq
    apply Subtype.ext
    have h := congrArg Subtype.val heq
    have hnat : z.val.toNat = v.val.toNat := Nat.eq_of_mul_eq_mul_left S.positive h
    obtain ⟨x, hx, hzx⟩ := z.property.1
    obtain ⟨y, hy, hvy⟩ := v.property.1
    simpa [hzx, hvy] using congrArg (fun n : ℕ ↦ (n : ℤ)) hnat
  have hsurj : Function.Surjective F := by
    intro w
    obtain ⟨x, hx, heq⟩ := (S.scale w.val).mp w.property.1
    have hs : IsIntegralSocle S.ideal (x : ℤ) :=
      (S.socle_iff x).mp (by simpa [← heq] using w.property)
    refine ⟨⟨x, hs⟩, ?_⟩
    apply Subtype.ext
    simpa [F] using heq.symm
  exact (Equiv.ofBijective F ⟨hinj, hsurj⟩).symm

/-- Forward division and inverse multiplication for minimal ideal generators. -/
noncomputable def generatorEquiv :
    {w // IsMinimalTailGenerator H (aperyTail Gamma H m) w} ≃
      {z // S.ideal.IsMinimalGenerator z} := by
  let F : {z // S.ideal.IsMinimalGenerator z} →
      {w // IsMinimalTailGenerator H (aperyTail Gamma H m) w} := fun z ↦
    ⟨S.d * z.val.toNat, (S.generator_iff z.val.toNat).mpr (by
      have hz := S.ideal_nonneg z.property.1
      simpa [Int.toNat_of_nonneg hz] using z.property)⟩
  have hinj : Function.Injective F := by
    intro z v heq
    apply Subtype.ext
    have h := congrArg Subtype.val heq
    have hnat : z.val.toNat = v.val.toNat := Nat.eq_of_mul_eq_mul_left S.positive h
    have hz := S.ideal_nonneg z.property.1
    have hv := S.ideal_nonneg v.property.1
    simpa [Int.toNat_of_nonneg hz, Int.toNat_of_nonneg hv] using
      congrArg (fun n : ℕ ↦ (n : ℤ)) hnat
  have hsurj : Function.Surjective F := by
    intro w
    obtain ⟨x, hx, heq⟩ := (S.scale w.val).mp w.property.1.1
    have hs : S.ideal.IsMinimalGenerator (x : ℤ) :=
      (S.generator_iff x).mp (by simpa [← heq] using w.property)
    refine ⟨⟨x, hs⟩, ?_⟩
    apply Subtype.ext
    simpa [F] using heq.symm
  exact (Equiv.ofBijective F ⟨hinj, hsurj⟩).symm

noncomputable def normalizationData : NormalizationData Gamma H m S.Hbar S.ideal where
  socleEquiv := S.socleEquiv
  generatorEquiv := S.generatorEquiv

theorem socleEquiv_symm_apply (z : {z // IsIntegralSocle S.ideal z}) :
    (S.socleEquiv.symm z).val = S.d * z.val.toNat := rfl

theorem generatorEquiv_symm_apply (z : {z // S.ideal.IsMinimalGenerator z}) :
    (S.generatorEquiv.symm z).val = S.d * z.val.toNat := rfl

theorem socleEquiv_apply (w : {w // IsSocle Gamma H m w}) :
    (S.socleEquiv w).val = (w.val / S.d : ℕ) := by
  have heq := congrArg Subtype.val (S.socleEquiv.symm_apply_apply w)
  rw [S.socleEquiv_symm_apply] at heq
  obtain ⟨x, hx, hz⟩ := (S.socleEquiv w).property.1
  simp only [hz, Int.toNat_natCast] at heq
  rw [hz, ← heq]
  congr 1
  exact (Nat.mul_div_cancel_left x S.positive).symm

theorem generatorEquiv_apply (w : {w // IsMinimalTailGenerator H (aperyTail Gamma H m) w}) :
    (S.generatorEquiv w).val = (w.val / S.d : ℕ) := by
  have heq := congrArg Subtype.val (S.generatorEquiv.symm_apply_apply w)
  rw [S.generatorEquiv_symm_apply] at heq
  obtain ⟨x, hx, hz⟩ := (S.generatorEquiv w).property.1
  simp only [hz, Int.toNat_natCast] at heq
  rw [hz, ← heq]
  congr 1
  exact (Nat.mul_div_cancel_left x S.positive).symm

end TailScaling

theorem aperyTail_nonempty_of_positive_generator
    {Gamma H : AddSubmonoid ℕ} {m n : ℕ}
    (hm : m ∈ Gamma) (hn : n ∈ H) (hnpos : 0 < n) :
    (aperyTail Gamma H m).Nonempty := by
  refine ⟨m * n, ?_, ?_, ?_⟩
  · exact H.nsmul_mem hn m
  · nlinarith
  · simpa [nsmul_eq_mul, Nat.sub_mul, Nat.mul_sub, Nat.mul_comm] using Gamma.nsmul_mem hm (n - 1)

/-- All inputs to the internal scaling interface are constructed from the
actual minimally four-generated presentation. -/
def buildTailScaling (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    TailScaling Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m where
  Hbar := normalizedSemigroup n₁ n₂ n₃ h.n₁_pos
  d := tailGcd n₁ n₂ n₃
  positive := tailGcd_pos h.n₁_pos
  scale := normalizedSemigroup_scale n₁ n₂ n₃ h.n₁_pos
  inclusion := by rw [h.generated]; exact generatedThree_le_generatedFour m n₁ n₂ n₃
  nonempty := aperyTail_nonempty_of_positive_generator
    (by rw [h.generated]; exact firstGenerator_mem_generatedFour m n₁ n₂ n₃)
    (AddSubmonoid.subset_closure (by simp)) h.n₁_pos

/-- The normalized Apéry-tail as a concrete relative ideal over the
gcd-normalized numerical semigroup. -/
def normalizedTailIdeal (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    RelativeIdeal (normalizedSemigroup n₁ n₂ n₃ h.n₁_pos) :=
  (buildTailScaling Gamma m n₁ n₂ n₃ h).ideal

theorem mem_normalizedTailIdeal_iff (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) (z : ℤ) :
    z ∈ normalizedTailIdeal Gamma m n₁ n₂ n₃ h ↔
      ∃ w : ℕ, w ∈ aperyTail Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m ∧
        (tailGcd n₁ n₂ n₃ : ℤ) * z = w :=
  (buildTailScaling Gamma m n₁ n₂ n₃ h).mem_ideal_iff z

/-- The formerly external normalization certificate, now constructed. -/
noncomputable def buildNormalizationData (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    NormalizationData Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m
      (normalizedSemigroup n₁ n₂ n₃ h.n₁_pos) (normalizedTailIdeal Gamma m n₁ n₂ n₃ h) :=
  (buildTailScaling Gamma m n₁ n₂ n₃ h).normalizationData

theorem normalizedTail_generatorCount (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    (normalizedTailIdeal Gamma m n₁ n₂ n₃ h).generatorCount =
      tailGeneratorCount (generatedThree n₁ n₂ n₃)
        (aperyTail Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m) :=
  (buildNormalizationData Gamma m n₁ n₂ n₃ h).generatorCount_eq.symm

theorem normalizedTail_socle_card (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    Nat.card {w // IsSocle Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m w} =
      Nat.card {z // IsIntegralSocle (normalizedTailIdeal Gamma m n₁ n₂ n₃ h) z} :=
  (buildNormalizationData Gamma m n₁ n₂ n₃ h).socle_natCard_eq

/-- The paper's normalization chain, with both normalized objects constructed. -/
theorem fourGenerated_normalization_chain (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    Gamma.asRelativeIdeal.idealType ≤ (normalizedTailIdeal Gamma m n₁ n₂ n₃ h).idealType ∧
    (normalizedTailIdeal Gamma m n₁ n₂ n₃ h).idealType ≤
      2 * tailGeneratorCount (generatedThree n₁ n₂ n₃)
        (aperyTail Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m) := by
  have ha := quotient_pos_of_dvd h.n₁_pos (tailGcd_dvd n₁ n₂ n₃).1
  let : NeZero (n₁ / tailGcd n₁ n₂ n₃) := ⟨Nat.ne_of_gt ha⟩
  have hmin := normalizedSemigroup_minimal h
  constructor
  · calc
      Gamma.asRelativeIdeal.idealType =
          Nat.card {w // IsSocle Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m w} :=
        fourGenerated_idealType_eq_natCard_socle Gamma m n₁ n₂ n₃ h.m_pos h.generated
      _ = Nat.card {z // IsIntegralSocle (normalizedTailIdeal Gamma m n₁ n₂ n₃ h) z} :=
        normalizedTail_socle_card Gamma m n₁ n₂ n₃ h
      _ ≤ (normalizedTailIdeal Gamma m n₁ n₂ n₃ h).idealType :=
        natCard_integralSocle_le_idealType _ _ _ _ hmin.1
  · rw [← normalizedTail_generatorCount Gamma m n₁ n₂ n₃ h]
    exact RelativeIdeal.idealType_le_two_mul_generatorCount _ _ _ _ hmin

/-- Normalization-complete four-generated bound: no normalization data are assumed. -/
theorem fourGenerated_bound_after_normalization (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    Gamma.asRelativeIdeal.idealType ≤
      2 * tailGeneratorCount (generatedThree n₁ n₂ n₃)
        (aperyTail Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m) := by
  obtain ⟨h₁, h₂⟩ := fourGenerated_normalization_chain Gamma m n₁ n₂ n₃ h
  exact h₁.trans h₂

/-- Only the separate minimal-presentation comparison remains as a hypothesis.
`rho` is an upper-bound parameter here, not a definition of presentation rank. -/
theorem fourGenerated_final_bound (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ rho : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃)
    (hmuTailRho : tailGeneratorCount (generatedThree n₁ n₂ n₃)
      (aperyTail Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m) ≤ rho) :
    Gamma.asRelativeIdeal.idealType ≤ 2 * rho :=
  (fourGenerated_bound_after_normalization Gamma m n₁ n₂ n₃ h).trans
    (Nat.mul_le_mul_left 2 hmuTailRho)

end NS25Lean.FourGeneratedBridge
