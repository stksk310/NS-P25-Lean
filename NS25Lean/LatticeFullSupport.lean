import NS25Lean.MonomialSetup

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3A
open MvPolynomial Presentation
open scoped MonomialOrder
variable {k : Type*} [Field k]

theorem monomial_mem_initial_iff (m : MonomialOrder (Fin 3))
    (I : Ideal (Polynomial k)) (a : Exponent) :
    monomial a (1 : k) ∈ L2B.monomialInitialIdeal k m I ↔
      ∃ f ∈ I, f ≠ 0 ∧ m.degree f ≤ a := by
  classical
  unfold L2B.monomialInitialIdeal
  rw [m.span_leadingTerm_eq_span_monomial']
  have he : (fun p : Polynomial k => monomial (m.degree p) (1 : k)) ''
      ((I : Set (Polynomial k)) \ {0}) = (fun u => monomial u (1 : k)) ''
      (m.degree '' ((I : Set (Polynomial k)) \ {0})) :=
    (Set.image_image (fun u => monomial u (1 : k)) m.degree
      ((I : Set (Polynomial k)) \ {0})).symm
  rw [he, monomial_mem_span_iff]
  simp only [Set.mem_image, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, ⟨f, ⟨hf, hz⟩, rfl⟩, hle⟩; exact ⟨f, hf, hz, hle⟩
  · rintro ⟨f, hf, hz, hle⟩; exact ⟨m.degree f, ⟨f, ⟨hf, hz⟩, rfl⟩, hle⟩

theorem initial_isMonomial (m : MonomialOrder (Fin 3)) (I : Ideal (Polynomial k)) :
    L2B.IsMonomialIdeal k (L2B.monomialInitialIdeal k m I) := by
  refine ⟨m.degree '' ((I : Set (Polynomial k)) \ {0}), ?_⟩
  unfold L2B.monomialInitialIdeal
  rw [m.span_leadingTerm_eq_span_monomial', Set.image_image]

variable {H : Type*} [AddCommGroup H]

def relationKernel (w : Fin 3 → H) : Ideal (Polynomial k) :=
  RingHom.ker (factorizationAlgebraMap k w).toRingHom

theorem lower_partner (w : Fin 3 → H) (m : MonomialOrder (Fin 3))
    (f : Polynomial k) (hf : f ∈ relationKernel w) (hz : f ≠ 0) :
    ∃ b, b ≺[m] m.degree f ∧ factorizationMap w b = factorizationMap w (m.degree f) := by
  classical
  have hsum := L2B.factorization_coeff_sum k w f (factorizationMap w (m.degree f))
  have hzero : factorizationAlgebraMap k w f = 0 := hf
  rw [hzero] at hsum
  have ha := m.degree_mem_support hz
  obtain ⟨b, hb, hne, he⟩ : ∃ b ∈ f.support, b ≠ m.degree f ∧
      factorizationMap w b = factorizationMap w (m.degree f) := by
    by_contra! hn
    have heval : (∑ b ∈ f.support,
        if factorizationMap w b = factorizationMap w (m.degree f) then coeff b f else 0) =
        coeff (m.degree f) f := by
      rw [Finset.sum_eq_single (m.degree f)]
      · simp
      · intro b hb hne; simp [hn b hb hne]
      · exact fun hn => (hn ha).elim
    rw [heval] at hsum
    exact (mem_support_iff.mp ha) hsum.symm
  refine ⟨b, lt_of_le_of_ne (m.le_degree hb) ?_, he⟩
  exact fun h => hne (m.toSyn.injective h)

theorem binomial_initial_mem (w : Fin 3 → H) (m : MonomialOrder (Fin 3))
    (a b : Exponent) (hlt : b ≺[m] a) (he : factorizationMap w a = factorizationMap w b) :
    monomial a (1 : k) ∈ L2B.monomialInitialIdeal k m (relationKernel w) := by
  classical
  have hdeg : m.degree (monomial b (1 : k)) ≺[m] m.degree (monomial a (1 : k)) := by
    simpa only [m.degree_monomial, one_ne_zero, ite_false] using hlt
  have hf : monomial a (1 : k) - monomial b 1 ∈ relationKernel w := by
    change factorizationAlgebraMap k w _ = 0
    simp only [map_sub, factorizationAlgebraMap_monomial, he, sub_self]
  have hlead : m.leadingTerm (monomial a (1 : k) - monomial b 1) = monomial a 1 := by
    rw [MonomialOrder.leadingTerm, m.degree_sub_of_lt hdeg, m.leadingCoeff_sub_of_lt hdeg]
    simp [m.degree_monomial]
  exact hlead ▸ Ideal.subset_span ⟨_, hf, rfl⟩

/-- Every actual minimal generator of the initial ideal has a binomial partner. -/
theorem minimal_has_partner (w : Fin 3 → H) (m : MonomialOrder (Fin 3)) (a : Exponent)
    (ha : a ∈ minimalExponents (L2B.monomialInitialIdeal k m (relationKernel w))) :
    ∃ b, b ≺[m] a ∧ factorizationMap w b = factorizationMap w a := by
  obtain ⟨f, hf, hz, hle⟩ := (monomial_mem_initial_iff m _ a).mp ha.1
  have hm : monomial (m.degree f) (1 : k) ∈
      L2B.monomialInitialIdeal k m (relationKernel w) :=
    (monomial_mem_initial_iff m _ _).mpr ⟨f, hf, hz, le_rfl⟩
  have heq : m.degree f = a := le_antisymm hle (ha.2 hm hle)
  simpa only [heq] using lower_partner w m f hf hz

theorem cancel_order (m : MonomialOrder (Fin 3)) (a b c : Exponent)
    (hca : c ≤ a) (hcb : c ≤ b) (h : b ≺[m] a) : b - c ≺[m] a - c := by
  have he : m.toSyn (b - c) + m.toSyn c < m.toSyn (a - c) + m.toSyn c := by
    simpa only [← map_add, tsub_add_cancel_of_le hca, tsub_add_cancel_of_le hcb] using h
  exact (add_lt_add_iff_right _).mp he

theorem cancel_relation (w : Fin 3 → H) (a b c : Exponent)
    (hca : c ≤ a) (hcb : c ≤ b) (he : factorizationMap w a = factorizationMap w b) :
    factorizationMap w (a - c) = factorizationMap w (b - c) := by
  apply add_right_cancel (b := factorizationMap w c)
  simpa only [← map_add, tsub_add_cancel_of_le hca, tsub_add_cancel_of_le hcb] using he

/-- No nonzero common monomial divisor survives minimality. -/
theorem minimal_partner_coprime (w : Fin 3 → H) (m : MonomialOrder (Fin 3))
    (a b : Exponent)
    (ha : a ∈ minimalExponents (L2B.monomialInitialIdeal k m (relationKernel w)))
    (hlt : b ≺[m] a) (he : factorizationMap w b = factorizationMap w a) :
    a ⊓ b = 0 := by
  let c := a ⊓ b
  have hca : c ≤ a := inf_le_left
  have hcb : c ≤ b := inf_le_right
  have hmem := binomial_initial_mem (k := k) w m (a - c) (b - c)
    (cancel_order m a b c hca hcb hlt) (cancel_relation w a b c hca hcb he.symm)
  have hle : a ≤ a - c := ha.2 hmem tsub_le_self
  ext i
  have h1 := hle i
  have h2 := hca i
  change a i ≤ a i - c i at h1
  change c i = 0
  omega

theorem fullSupport_partner_zero (a b : Exponent) (ha : FullSupport a) (hc : a ⊓ b = 0) :
    b = 0 := by
  ext i
  have h := congrArg (fun u : Exponent => u i) hc
  have hp := ha i
  change min (a i) (b i) = 0 at h
  change b i = 0
  omega

theorem fullSupport_maps_zero (w : Fin 3 → H) (m : MonomialOrder (Fin 3))
    (a : Exponent)
    (ha : a ∈ fullSupportGenerators (L2B.monomialInitialIdeal k m (relationKernel w))) :
    factorizationMap w a = 0 := by
  obtain ⟨b, hlt, he⟩ := minimal_has_partner w m a ha.1
  have hz := fullSupport_partner_zero a b ha.2 (minimal_partner_coprime w m a b ha.1 hlt he)
  simpa only [hz, map_zero] using he.symm

/-- General full-support rigidity for kernels into arbitrary additive groups. -/
theorem fullSupport_unique (w : Fin 3 → H) (m : MonomialOrder (Fin 3))
    (a b : Exponent)
    (ha : a ∈ fullSupportGenerators (L2B.monomialInitialIdeal k m (relationKernel w)))
    (hb : b ∈ fullSupportGenerators (L2B.monomialInitialIdeal k m (relationKernel w))) : a = b := by
  have he : factorizationMap w a = factorizationMap w b :=
    (fullSupport_maps_zero w m a ha).trans (fullSupport_maps_zero w m b hb).symm
  have impossible (u v : Exponent)
      (hu : u ∈ fullSupportGenerators (L2B.monomialInitialIdeal k m (relationKernel w)))
      (hv : FullSupport v) (hlt : v ≺[m] u)
      (heq : factorizationMap w v = factorizationMap w u) : False := by
    have hz := fullSupport_partner_zero u v hu.2 (minimal_partner_coprime w m u v hu.1 hlt heq)
    have hp := hv 0
    simp only [hz, Finsupp.zero_apply] at hp
    omega
  rcases lt_trichotomy (m.toSyn a) (m.toSyn b) with h | h | h
  · exact (impossible b a hb ha.2 h he).elim
  · exact m.toSyn.injective h
  · exact (impossible a b ha hb.2 h he.symm).elim

theorem q_fs_relationKernel_le_one (w : Fin 3 → H) (m : MonomialOrder (Fin 3)) :
    q_fs (L2B.monomialInitialIdeal k m (relationKernel w)) ≤ 1 := by
  apply (Set.ncard_le_one (fullSupportGenerators_finite _)).mpr
  intro a ha b hb
  exact fullSupport_unique w m a b ha hb

/-- An arbitrary lattice, with the same binomial-span definition as frozen L2-B. -/
def latticeIdeal (L : AddSubgroup (Fin 3 →₀ ℤ)) : Ideal (Polynomial k) :=
  Ideal.span ((fun p : Exponent × Exponent => monomial p.1 (1 : k) - monomial p.2 1) ''
    {p | L2B.exponentDifference p.1 p.2 ∈ L})

def quotientWeights (L : AddSubgroup (Fin 3 →₀ ℤ)) : Fin 3 → (Fin 3 →₀ ℤ) ⧸ L :=
  fun i => QuotientAddGroup.mk (Finsupp.single i 1)

theorem quotient_factorization (L : AddSubgroup (Fin 3 →₀ ℤ)) (a : Exponent) :
    factorizationMap (quotientWeights L) a =
      QuotientAddGroup.mk (a.mapRange (Nat.castAddMonoidHom ℤ) (by simp)) := by
  have he : factorizationMap (quotientWeights L) =
      (QuotientAddGroup.mk' L).comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)) := by
    apply Finsupp.addHom_ext
    intro i n
    simp only [factorizationMap_single, AddMonoidHom.coe_comp, QuotientAddGroup.coe_mk',
      Function.comp_apply, Finsupp.mapRange.addMonoidHom_apply, Nat.coe_castAddMonoidHom,
      Finsupp.mapRange_single]
    change n • (QuotientAddGroup.mk' L) (Finsupp.single i 1) =
      (QuotientAddGroup.mk' L) (Finsupp.single i (n : ℤ))
    rw [← map_nsmul]
    congr 1
    simp
  exact DFunLike.congr_fun he a

theorem latticeIdeal_eq_relationKernel (L : AddSubgroup (Fin 3 →₀ ℤ)) :
    latticeIdeal (k := k) L = relationKernel (quotientWeights L) := by
  rw [relationKernel, ← relationIdeal_factorization_eq_ker]
  unfold latticeIdeal relationIdeal
  congr 1
  congr 1
  ext p
  change L2B.exponentDifference p.1 p.2 ∈ L ↔
    factorizationMap (quotientWeights L) p.1 = factorizationMap (quotientWeights L) p.2
  rw [quotient_factorization, quotient_factorization, QuotientAddGroup.eq_iff_sub_mem]
  rfl

/-- Paper Proposition 4.2, for every lattice and every actual monomial order. -/
theorem q_fs_lattice_initial_le_one (L : AddSubgroup (Fin 3 →₀ ℤ))
    (m : MonomialOrder (Fin 3)) :
    q_fs (L2B.monomialInitialIdeal k m (latticeIdeal L)) ≤ 1 := by
  rw [latticeIdeal_eq_relationKernel]
  exact q_fs_relationKernel_le_one _ m

theorem relation_initial_proper (w : Fin 3 → H) (m : MonomialOrder (Fin 3)) :
    L2B.monomialInitialIdeal k m (relationKernel w) ≠ ⊤ := by
  intro ht
  have hmem : monomial (0 : Exponent) (1 : k) ∈
      L2B.monomialInitialIdeal k m (relationKernel w) := by rw [ht]; trivial
  obtain ⟨f, hf, hz, hle⟩ := (monomial_mem_initial_iff m _ _).mp hmem
  obtain ⟨b, hb, _⟩ := lower_partner w m f hf hz
  have he : m.degree f = 0 := le_antisymm hle zero_le
  rw [he] at hb
  exact (not_lt_of_ge (m.toSyn_monotone (show 0 ≤ b from zero_le))) hb

theorem lattice_initial_proper (L : AddSubgroup (Fin 3 →₀ ℤ)) (m : MonomialOrder (Fin 3)) :
    L2B.monomialInitialIdeal k m (latticeIdeal L) ≠ ⊤ := by
  rw [latticeIdeal_eq_relationKernel]
  exact relation_initial_proper _ m

end NS25Lean.L3A
