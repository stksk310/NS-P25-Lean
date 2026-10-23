import NS25Lean.AppendixBCompleteIntersection

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4B
open ChosenBase L2C L4A FourGeneratedBridge

private theorem pair_nonneg {a b : ℕ} {z : ℤ} (hz : twoGeneratorInt a b z) : 0 ≤ z := by
  obtain ⟨r, s, rfl⟩ := hz
  positivity

private theorem pair_add {a b : ℕ} {x y : ℤ}
    (hx : twoGeneratorInt a b x) (hy : twoGeneratorInt a b y) :
    twoGeneratorInt a b (x + y) := by
  obtain ⟨r, s, rfl⟩ := hx
  obtain ⟨k, l, rfl⟩ := hy
  exact ⟨r + k, s + l, by push_cast; ring⟩

private theorem pair_mul {a b : ℕ} {x t : ℤ}
    (hx : twoGeneratorInt a b x) (ht : 0 ≤ t) : twoGeneratorInt a b (x * t) := by
  obtain ⟨r, s, rfl⟩ := hx
  refine ⟨r * t.toNat, s * t.toNat, ?_⟩
  simp only [Nat.cast_mul, Int.toNat_of_nonneg ht]
  ring

private theorem pair_tail {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    {z : ℤ} (hz : (a : ℤ) * b - a - b < z) : twoGeneratorInt a b z := by
  have hnot : ¬twoGeneratorInt a b ((a : ℤ) * b - a - b - z) := by
    intro h
    have := pair_nonneg h
    omega
  have h := (two_generator_symmetry a b ha hb hc _).mp hnot
  convert h using 1; ring

variable {Gamma : NumericalSemigroup} {B : Data Gamma}

/-- The actual four-generator semigroup is the sum of the two scaled pair semigroups. -/
theorem normalizedPairs_intMem_iff (N : NormalizedPairs B) (z : ℤ) :
    IntMem Gamma.toAddSubmonoid z ↔ ∃ x y : ℤ,
      twoGeneratorInt N.alpha N.beta x ∧ twoGeneratorInt N.gamma N.delta y ∧
      z = (N.u : ℤ) * x + (N.v : ℤ) * y := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨f⟩ := L2C.fiber_nonempty B ⟨n, hn⟩
    refine ⟨(N.alpha : ℤ) * f.val (N.perm 0) + N.beta * f.val (N.perm 1),
      (N.gamma : ℤ) * f.val (N.perm 2) + N.delta * f.val (N.perm 3),
      ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ?_⟩
    exact_mod_cast (f.property.symm.trans (N.weight_expansion f.val))
  · rintro ⟨x, y, ⟨r, s, rfl⟩, ⟨k, l, rfl⟩, hz⟩
    have hm (i : Fin 4) (t : ℕ) : weights B i * t ∈ Gamma.toAddSubmonoid := by
      simpa [nsmul_eq_mul, mul_comm, weights] using
        Gamma.toAddSubmonoid.nsmul_mem (B.family i).property t
    have hmem := Gamma.toAddSubmonoid.add_mem
      (Gamma.toAddSubmonoid.add_mem (hm (N.perm 0) r) (hm (N.perm 1) s))
      (Gamma.toAddSubmonoid.add_mem (hm (N.perm 2) k) (hm (N.perm 3) l))
    rw [N.weight0, N.weight1, N.weight2, N.weight3] at hmem
    refine ⟨_, hmem, ?_⟩
    push_cast
    nlinarith [hz]

private theorem pair_apery_rep (N : NormalizedPairs B) (z : ℤ) :
    ∃ x y : ℤ, twoGeneratorInt N.alpha N.beta x ∧
      ¬twoGeneratorInt N.alpha N.beta (x - N.v) ∧
      z = (N.u : ℤ) * x + (N.v : ℤ) * y := by
  classical
  obtain ⟨x₀, y₀, hx₀, hxv, hz⟩ :=
    two_generator_normal_form N.v N.u N.v_pos N.uv_coprime.symm z
  have hv : (1 : ℤ) ≤ N.v := by exact_mod_cast N.v_pos
  have ha : (0 : ℤ) < N.alpha := by exact_mod_cast (show 0 < N.alpha by have := N.alpha_ge; omega)
  have hb : (0 : ℤ) < N.beta := by exact_mod_cast (show 0 < N.beta by have := N.beta_ge; omega)
  have hex : ∃ t : ℕ, twoGeneratorInt N.alpha N.beta (x₀ + (N.v : ℤ) * t) := by
    refine ⟨N.alpha * N.beta, pair_tail (by have := N.alpha_ge; omega)
      (by have := N.beta_ge; omega) N.ab_coprime ?_⟩
    push_cast
    nlinarith [mul_nonneg (show 0 ≤ (N.v : ℤ) - 1 by omega)
      (mul_nonneg (le_of_lt ha) (le_of_lt hb))]
  let t := Nat.find hex
  have ht : twoGeneratorInt N.alpha N.beta (x₀ + (N.v : ℤ) * t) := Nat.find_spec hex
  refine ⟨x₀ + (N.v : ℤ) * t, y₀ - (N.u : ℤ) * t, ht, ?_, ?_⟩
  · intro hsub
    by_cases hzero : t = 0
    · have hn := pair_nonneg hsub
      simp only [hzero, Nat.cast_zero, mul_zero, add_zero] at hn
      omega
    · have hlt : t - 1 < Nat.find hex := by change t - 1 < t; omega
      apply Nat.find_min hex hlt
      convert hsub using 1
      have hcast : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by omega
      rw [hcast]
      ring
  · nlinarith [hz]

private theorem gluing_normal_mem_iff (N : NormalizedPairs B)
    (hv : twoGeneratorInt N.alpha N.beta N.v)
    (hu : twoGeneratorInt N.gamma N.delta N.u)
    {x y z : ℤ} (hx : twoGeneratorInt N.alpha N.beta x)
    (hxv : ¬twoGeneratorInt N.alpha N.beta (x - N.v))
    (hz : z = (N.u : ℤ) * x + (N.v : ℤ) * y) :
    IntMem Gamma.toAddSubmonoid z ↔ twoGeneratorInt N.gamma N.delta y := by
  constructor
  · intro hm
    obtain ⟨p, q, hp, hq, he⟩ := (normalizedPairs_intMem_iff N z).mp hm
    have hd : (N.v : ℤ) ∣ p - x := N.uv_coprime.symm.isCoprime.dvd_of_dvd_mul_left
      ⟨y - q, by nlinarith [hz, he]⟩
    obtain ⟨t, ht⟩ := hd
    have hvpos : (0 : ℤ) < N.v := by exact_mod_cast N.v_pos
    have hy : y = q + (N.u : ℤ) * t := by nlinarith [hz, he, ht]
    have ht0 : 0 ≤ t := by
      by_contra hneg
      have h := pair_add hp (pair_mul hv (show 0 ≤ -t - 1 by omega))
      apply hxv
      convert h using 1; nlinarith [ht]
    rw [hy]
    exact pair_add hq (pair_mul hu ht0)
  · intro hy
    exact (normalizedPairs_intMem_iff N z).mpr ⟨x, y, hx, hy, hz⟩

/-- Integer Frobenius symmetry from the normalization and the two actual cross relations. -/
theorem normalizedPairs_gluing_symmetry (N : NormalizedPairs B)
    (hv : twoGeneratorInt N.alpha N.beta N.v)
    (hu : twoGeneratorInt N.gamma N.delta N.u) (z : ℤ) :
    ¬IntMem Gamma.toAddSubmonoid z ↔ IntMem Gamma.toAddSubmonoid
      ((N.u : ℤ) * ((N.alpha : ℤ) * N.beta - N.alpha - N.beta) +
        (N.v : ℤ) * ((N.gamma : ℤ) * N.delta - N.gamma - N.delta) +
        (N.u : ℤ) * N.v - z) := by
  obtain ⟨x, y, hx, hxv, hz⟩ := pair_apery_rep N z
  let F₁ : ℤ := (N.alpha : ℤ) * N.beta - N.alpha - N.beta
  let F₂ : ℤ := (N.gamma : ℤ) * N.delta - N.gamma - N.delta
  have sym₁ := two_generator_symmetry N.alpha N.beta
    (show 0 < N.alpha by have := N.alpha_ge; omega)
    (show 0 < N.beta by have := N.beta_ge; omega) N.ab_coprime
  have hx' : twoGeneratorInt N.alpha N.beta (F₁ + N.v - x) := by
    convert (sym₁ (x - N.v)).mp hxv using 1; dsimp [F₁]; ring
  have hxv' : ¬twoGeneratorInt N.alpha N.beta (F₁ + N.v - x - N.v) := by
    intro hm
    have hn := (sym₁ x).mpr (by convert hm using 1; dsimp [F₁]; ring)
    exact hn hx
  have he : (N.u : ℤ) * F₁ + (N.v : ℤ) * F₂ + (N.u : ℤ) * N.v - z =
      (N.u : ℤ) * (F₁ + N.v - x) + (N.v : ℤ) * (F₂ - y) := by nlinarith [hz]
  rw [gluing_normal_mem_iff N hv hu hx hxv hz,
    gluing_normal_mem_iff N hv hu hx' hxv' he]
  exact two_generator_symmetry N.gamma N.delta (by have := N.gamma_ge; omega)
    (by have := N.delta_ge; omega) N.cd_coprime y

/-- Symmetry forces the integer pseudo-Frobenius set to be a singleton. -/
theorem pseudoFrobeniusInt_iff_eq_of_symmetry (Gamma : NumericalSemigroup) (F : ℤ)
    (hsym : ∀ z : ℤ, ¬IntMem Gamma.toAddSubmonoid z ↔ IntMem Gamma.toAddSubmonoid (F - z))
    (f : ℤ) : IsPseudoFrobeniusInt Gamma.toAddSubmonoid f ↔ f = F := by
  have hF : ¬IntMem Gamma.toAddSubmonoid F := by
    intro hm
    have hzero := (hsym 0).mpr (by simpa using hm)
    exact hzero ⟨0, Gamma.toAddSubmonoid.zero_mem, by simp⟩
  constructor
  · rintro ⟨hf, hpf⟩
    obtain ⟨g, hg, hfg⟩ := (hsym f).mp hf
    by_cases hg0 : g = 0
    · simp only [hg0, Nat.cast_zero] at hfg
      omega
    · have hm := hpf g hg hg0
      apply False.elim
      apply hF
      convert hm using 1; omega
  · rintro rfl
    refine ⟨hF, ?_⟩
    intro g hg hg0
    have hneg : ¬IntMem Gamma.toAddSubmonoid (-(g : ℤ)) := by
      rintro ⟨n, hn, he⟩
      have : (0 : ℤ) < g := by exact_mod_cast (Nat.pos_of_ne_zero hg0)
      omega
    simpa using (hsym (-(g : ℤ))).mp hneg

theorem idealType_eq_one_of_symmetry (Gamma : NumericalSemigroup) (F : ℤ)
    (hsym : ∀ z : ℤ, ¬IntMem Gamma.toAddSubmonoid z ↔ IntMem Gamma.toAddSubmonoid (F - z)) :
    Gamma.asRelativeIdeal.idealType = 1 := by
  rw [← natCard_pseudoFrobeniusInt_eq_idealType Gamma, Nat.card_eq_one_iff_unique]
  have hp := pseudoFrobeniusInt_iff_eq_of_symmetry Gamma F hsym
  constructor
  · refine ⟨?_⟩
    intro a b
    apply Subtype.ext
    exact ((hp a.val).mp a.property).trans ((hp b.val).mp b.property).symm
  · exact ⟨⟨F, (hp F).mpr rfl⟩⟩

/-- The complete-intersection branch has type one, independently of the strict bound. -/
theorem completeIntersectionFour_type_eq_one
    {Gamma : NumericalSemigroup} (B : ChosenBase.Data Gamma)
    (hCI : L4A.IsCompleteIntersectionFour B) : Gamma.asRelativeIdeal.idealType = 1 := by
  obtain ⟨D⟩ := hCI ℚ
  apply idealType_eq_one_of_symmetry Gamma
    ((D.normalization.u : ℤ) * ((D.normalization.alpha : ℤ) * D.normalization.beta -
      D.normalization.alpha - D.normalization.beta) +
      (D.normalization.v : ℤ) * ((D.normalization.gamma : ℤ) * D.normalization.delta -
      D.normalization.gamma - D.normalization.delta) + (D.normalization.u : ℤ) * D.normalization.v)
  exact normalizedPairs_gluing_symmetry D.normalization
    ⟨D.r, D.s, by exact_mod_cast D.cross_v⟩ ⟨D.k, D.l, by exact_mod_cast D.cross_u⟩

/-- The source complete-intersection branch has the pair `(rho,type) = (3,1)`. -/
theorem completeIntersectionFour_rho_type
    {Gamma : NumericalSemigroup} (B : ChosenBase.Data Gamma)
    (hCI : L4A.IsCompleteIntersectionFour B) :
    (Presentation.rho Gamma, Gamma.asRelativeIdeal.idealType) = (3, 1) := by
  exact Prod.ext (L4A.completeIntersectionFour_rho hCI) (completeIntersectionFour_type_eq_one B hCI)

end NS25Lean.L4B
