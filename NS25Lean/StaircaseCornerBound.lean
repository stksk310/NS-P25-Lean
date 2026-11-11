import NS25Lean.MonomialStaircase

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3A.Staircase
open MvPolynomial
variable {k : Type*} [Field k]

theorem upward (I : Ideal (Polynomial k)) {a b : Exponent}
    (ha : monomial a (1 : k) ∈ I) (hab : a ≤ b) : monomial b (1 : k) ∈ I := by
  have h := I.mul_mem_left (monomial (b - a) (1 : k)) ha
  simpa only [monomial_mul, one_mul, tsub_add_cancel_of_le hab] using h

theorem downward (I : Ideal (Polynomial k)) {a b : Exponent}
    (hb : b ∈ standardExponents I) (hab : a ≤ b) : a ∈ standardExponents I :=
  fun ha => hb (upward I ha hab)

theorem socle_eq_of_le (I : Ideal (Polynomial k)) {a b : Exponent}
    (ha : a ∈ socleExponents I) (hb : b ∈ standardExponents I) (hab : a ≤ b) : a = b := by
  apply le_antisymm hab
  intro i
  by_contra! hi
  apply hb
  apply upward I (ha.2 i)
  intro j
  by_cases hji : j = i
  · subst j
    simpa using hi
  · simpa [Finsupp.single_apply, hji] using hab j

def level (p : Exponent) (n : ℕ) : Exponent := p.update 2 n

@[simp] theorem level_zero (p : Exponent) (n : ℕ) : level p n 0 = p 0 := by
  simp [level, Finsupp.update_apply]
@[simp] theorem level_one (p : Exponent) (n : ℕ) : level p n 1 = p 1 := by
  simp [level, Finsupp.update_apply]
@[simp] theorem level_two (p : Exponent) (n : ℕ) : level p n 2 = n := by
  simp [level, Finsupp.update_apply]
@[simp] theorem level_self (p : Exponent) : level p (p 2) = p := Finsupp.update_self p 2

theorem level_le (p : Exponent) {n : ℕ} (hn : n ≤ p 2) : level p n ≤ p := by
  intro i
  fin_cases i <;> simp <;> omega

def Corner (I : Ideal (Polynomial k)) (a : Exponent) : Prop :=
  a ∈ standardExponents I ∧ monomial (a + Finsupp.single 0 1) (1 : k) ∈ I ∧
    monomial (a + Finsupp.single 1 1) (1 : k) ∈ I

theorem corner_eq_of_x (I : Ideal (Polynomial k)) {a b : Exponent}
    (ha : Corner I a) (hb : Corner I b) (hx : a 0 = b 0) (hz : a 2 = b 2) : a = b := by
  have hy : a 1 = b 1 := by
    apply le_antisymm
    · by_contra! h
      apply ha.1
      apply upward I hb.2.2
      intro j
      fin_cases j <;> simp [Finsupp.single_apply] <;> omega
    · by_contra! h
      apply hb.1
      apply upward I ha.2.2
      intro j
      fin_cases j <;> simp [Finsupp.single_apply] <;> omega
  ext j
  fin_cases j <;> assumption

theorem corner_eq_of_y (I : Ideal (Polynomial k)) {a b : Exponent}
    (ha : Corner I a) (hb : Corner I b) (hy : a 1 = b 1) (hz : a 2 = b 2) : a = b := by
  have hx : a 0 = b 0 := by
    apply le_antisymm
    · by_contra! h
      apply ha.1
      apply upward I hb.2.1
      intro j
      fin_cases j <;> simp [Finsupp.single_apply] <;> omega
    · by_contra! h
      apply hb.1
      apply upward I ha.2.1
      intro j
      fin_cases j <;> simp [Finsupp.single_apply] <;> omega
  ext j
  fin_cases j <;> assumption

theorem exists_corner (I : Ideal (Polynomial k)) (p : socleExponents I) :
    ∃ n, Corner I (level p.val n) := by
  refine ⟨p.val 2, ?_⟩
  simpa [Corner] using ⟨p.property.1, p.property.2 0, p.property.2 1⟩

def birth (I : Ideal (Polynomial k)) (p : socleExponents I) : ℕ := by
  classical
  exact Nat.find (exists_corner I p)

theorem birth_corner (I : Ideal (Polynomial k)) (p : socleExponents I) :
    Corner I (level p.val (birth I p)) := by
  classical
  exact Nat.find_spec (exists_corner I p)

theorem birth_le (I : Ideal (Polynomial k)) (p : socleExponents I) : birth I p ≤ p.val 2 := by
  classical
  apply Nat.find_min' (exists_corner I p)
  simpa [Corner] using ⟨p.property.1, p.property.2 0, p.property.2 1⟩

theorem neighbor_generator (I : Ideal (Polynomial k)) (p : Exponent) (n : ℕ)
    (i : Fin 3) (hi : i ≠ 2) (hs : level p n ∈ standardExponents I)
    (hm : monomial (level p n + Finsupp.single i 1) (1 : k) ∈ I)
    (hp : n = 0 ∨ monomial (level p (n - 1) + Finsupp.single i 1) (1 : k) ∉ I) :
    ∃ g ∈ minimalExponents I, g i = p i + 1 ∧ g 2 = n := by
  obtain ⟨g, hle, hg⟩ := exists_minimal_le I _ hm
  have hgi : g i = level p n i + 1 := by
    have hu := hle i
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hu
    have hn : ¬g i ≤ level p n i := by
      intro h
      apply hs
      apply upward I hg.1
      intro j
      by_cases hji : j = i
      · subst j; exact h
      · simpa [Finsupp.single_apply, hji] using hle j
    omega
  have hgz : g 2 = n := by
    have hu : g 2 ≤ n := by simpa [Finsupp.single_apply, Ne.symm hi] using hle 2
    rcases hp with rfl | hp
    · omega
    · by_contra hne
      have hlt : g 2 < n := by omega
      apply hp
      apply upward I hg.1
      intro j
      by_cases hj : j = 2
      · subst j
        simp [Finsupp.single_apply, Ne.symm hi]
        omega
      · simpa [level, Finsupp.update_apply, hj] using hle j
  refine ⟨g, hg, ?_, hgz⟩
  simpa [level, Finsupp.update_apply, hi] using hgi

theorem birth_generator (I : Ideal (Polynomial k)) (p : socleExponents I) :
    ∃ i : Fin 3, ∃ g ∈ minimalExponents I,
      (i = 0 ∨ i = 1) ∧ g i = p.val i + 1 ∧ g 2 = birth I p ∧
        (i = 1 → 0 < birth I p) := by
  classical
  have hc := birth_corner I p
  by_cases hz : birth I p = 0
  · obtain ⟨g, hg, hgi, hgz⟩ := neighbor_generator I p.val (birth I p) 0
      (by decide) hc.1 hc.2.1 (Or.inl hz)
    exact ⟨0, g, hg, Or.inl rfl, hgi, hgz, by simp⟩
  · have hpos : 0 < birth I p := Nat.pos_of_ne_zero hz
    have hs : level p.val (birth I p - 1) ∈ standardExponents I :=
      downward I p.property.1 (level_le _ (by have := birth_le I p; omega))
    have hn : ¬Corner I (level p.val (birth I p - 1)) :=
      Nat.find_min (exists_corner I p) (by change birth I p - 1 < birth I p; omega)
    by_cases h0 : monomial (level p.val (birth I p - 1) + Finsupp.single 0 1) (1 : k) ∈ I
    · have h1 : monomial (level p.val (birth I p - 1) + Finsupp.single 1 1) (1 : k) ∉ I :=
        fun h1 => hn ⟨hs, h0, h1⟩
      obtain ⟨g, hg, hgi, hgz⟩ := neighbor_generator I p.val (birth I p) 1
        (by decide) hc.1 hc.2.2 (Or.inr h1)
      exact ⟨1, g, hg, Or.inr rfl, hgi, hgz, fun _ => hpos⟩
    · obtain ⟨g, hg, hgi, hgz⟩ := neighbor_generator I p.val (birth I p) 0
        (by decide) hc.1 hc.2.1 (Or.inr h0)
      exact ⟨0, g, hg, Or.inl rfl, hgi, hgz, by simp⟩

/-- The first copy omits the pure y and pure z generators. -/
def mainGenerators (I : Ideal (Polynomial k)) : Set Exponent :=
  {g | g ∈ minimalExponents I ∧ (0 < g 0 ∨ (0 < g 1 ∧ 0 < g 2))}

theorem mainGenerators_finite (I : Ideal (Polynomial k)) : (mainGenerators I).Finite :=
  (minimalExponents_finite I).subset (fun _ h => h.1)

abbrev Tags (I : Ideal (Polynomial k)) := mainGenerators I ⊕ fullSupportGenerators I

def tagExponent (I : Ideal (Polynomial k)) : Tags I → Exponent
  | Sum.inl g => g.val
  | Sum.inr g => g.val

def tagCoordinate (I : Ideal (Polynomial k)) : Tags I → Fin 3
  | Sum.inl g => if 0 < g.val 0 then 0 else 1
  | Sum.inr _ => 1

theorem tagCoordinate_cases (I : Ideal (Polynomial k)) (t : Tags I) :
    tagCoordinate I t = 0 ∨ tagCoordinate I t = 1 := by
  cases t with
  | inl g => simp only [tagCoordinate]; split <;> simp
  | inr g => exact Or.inr rfl

theorem exists_tag (I : Ideal (Polynomial k)) (p : socleExponents I) :
    ∃ t : Tags I, tagExponent I t 2 = birth I p ∧
      tagExponent I t (tagCoordinate I t) = p.val (tagCoordinate I t) + 1 := by
  classical
  obtain ⟨i, g, hg, hi, hgi, hgz, hp⟩ := birth_generator I p
  rcases hi with rfl | rfl
  · have hx : 0 < g 0 := by omega
    refine ⟨Sum.inl ⟨g, hg, Or.inl hx⟩, ?_⟩
    simpa [tagExponent, tagCoordinate, hx] using And.intro hgz hgi
  · have hy : 0 < g 1 := by omega
    have hz : 0 < g 2 := by have := hp rfl; omega
    by_cases hx : 0 < g 0
    · have hf : FullSupport g := by intro j; fin_cases j <;> assumption
      exact ⟨Sum.inr ⟨g, hg, hf⟩, hgz, hgi⟩
    · refine ⟨Sum.inl ⟨g, hg, Or.inr ⟨hy, hz⟩⟩, ?_⟩
      simpa [tagExponent, tagCoordinate, hx] using And.intro hgz hgi

def tag (I : Ideal (Polynomial k)) (p : socleExponents I) : Tags I :=
  Classical.choose (exists_tag I p)

theorem tag_spec (I : Ideal (Polynomial k)) (p : socleExponents I) :
    tagExponent I (tag I p) 2 = birth I p ∧
      tagExponent I (tag I p) (tagCoordinate I (tag I p)) =
        p.val (tagCoordinate I (tag I p)) + 1 := Classical.choose_spec (exists_tag I p)

theorem socle_eq_of_horizontal (I : Ideal (Polynomial k)) (p q : socleExponents I)
    (hx : p.val 0 = q.val 0) (hy : p.val 1 = q.val 1) : p = q := by
  apply Subtype.ext
  rcases le_total (p.val 2) (q.val 2) with hz | hz
  · apply socle_eq_of_le I p.property q.property.1
    intro j
    fin_cases j <;> simp_all
  · symm
    apply socle_eq_of_le I q.property p.property.1
    intro j
    fin_cases j <;> simp_all

theorem tag_injective_of_spec (I : Ideal (Polynomial k))
    (f : socleExponents I → Tags I)
    (hf : ∀ p, tagExponent I (f p) 2 = birth I p ∧
      tagExponent I (f p) (tagCoordinate I (f p)) =
        p.val (tagCoordinate I (f p)) + 1) : Function.Injective f := by
  intro p q he
  have hsp := hf p
  have hsq := hf q
  rw [← he] at hsq
  have hz : birth I p = birth I q := hsp.1.symm.trans hsq.1
  have hc : p.val (tagCoordinate I (f p)) = q.val (tagCoordinate I (f p)) := by omega
  have hl : level p.val (birth I p) = level q.val (birth I q) := by
    rcases tagCoordinate_cases I (f p) with hi | hi
    · apply corner_eq_of_x I (birth_corner I p) (birth_corner I q)
      · simpa [hi] using hc
      · simpa using hz
    · apply corner_eq_of_y I (birth_corner I p) (birth_corner I q)
      · simpa [hi] using hc
      · simpa using hz
  apply socle_eq_of_horizontal I p q
  · simpa using congrArg (fun a : Exponent => a 0) hl
  · simpa using congrArg (fun a : Exponent => a 1) hl

/-- The literal classical-choice map is one permitted birth-height tagging. -/
theorem tag_injective (I : Ideal (Polynomial k)) : Function.Injective (tag I) :=
  tag_injective_of_spec I (tag I) (tag_spec I)

theorem socle_count_le_tags (I : Ideal (Polynomial k)) :
    (socleExponents I).ncard ≤ (mainGenerators I).ncard + (fullSupportGenerators I).ncard := by
  letI : Finite (mainGenerators I) := (mainGenerators_finite I).to_subtype
  letI : Finite (fullSupportGenerators I) := (fullSupportGenerators_finite I).to_subtype
  have h := Nat.card_le_card_of_injective (tag I) (tag_injective I)
  simpa only [Tags, Nat.card_sum, Nat.card_coe_set_eq] using h

theorem pure_minimal (M : ArtinianMonomial k) (i : Fin 3) :
    ∃ g ∈ minimalExponents M.ideal, 0 < g i ∧ ∀ j, j ≠ i → g j = 0 := by
  letI := M.artinian
  obtain ⟨n, hn⟩ := exists_purePower_mem M.ideal M.monomial i
  obtain ⟨g, hle, hg⟩ := exists_minimal_le M.ideal _ hn
  have hoff : ∀ j, j ≠ i → g j = 0 := by
    intro j hj
    have h := hle j
    simpa [Finsupp.single_apply, hj] using h
  refine ⟨g, hg, ?_, hoff⟩
  by_contra! hz
  have he : g = 0 := by
    ext j
    by_cases hj : j = i
    · subst j; simpa using hz
    · simpa using hoff j hj
  apply M.proper
  apply (Ideal.eq_top_iff_one _).mpr
  have h := hg.1
  simpa [he] using h

theorem main_count_add_two_le (M : ArtinianMonomial k) :
    (mainGenerators M.ideal).ncard + 2 ≤ (minimalExponents M.ideal).ncard := by
  classical
  obtain ⟨gy, hgy, hgypos, hgyoff⟩ := pure_minimal M 1
  obtain ⟨gz, hgz, hgzpos, hgzoff⟩ := pure_minimal M 2
  have hy0 := hgyoff 0 (by decide)
  have hy2 := hgyoff 2 (by decide)
  have hz0 := hgzoff 0 (by decide)
  have hz1 := hgzoff 1 (by decide)
  have hyn : gy ∉ mainGenerators M.ideal := by
    rintro ⟨_, h | h⟩ <;> omega
  have hzn : gz ∉ mainGenerators M.ideal := by
    rintro ⟨_, h | h⟩ <;> omega
  have hne : gy ≠ gz := by
    intro he
    have := congrArg (fun g : Exponent => g 1) he
    omega
  have hsub : insert gy (insert gz (mainGenerators M.ideal)) ⊆ minimalExponents M.ideal := by
    intro a ha
    rcases ha with rfl | ha
    · exact hgy
    rcases ha with rfl | ha
    · exact hgz
    · exact ha.1
  have hcard := Set.ncard_le_ncard hsub (minimalExponents_finite M.ideal)
  rw [Set.ncard_insert_of_notMem (by simp [hne, hyn])
      ((mainGenerators_finite M.ideal).insert gz),
    Set.ncard_insert_of_notMem hzn (mainGenerators_finite M.ideal)] at hcard
  omega

end NS25Lean.L3A.Staircase

namespace NS25Lean.L3A
variable {k : Type*} [Field k]

/-- General three-variable staircase bound, proved by birth-height tagging of corners. -/
theorem staircase_corner_bound (M : ArtinianMonomial k) :
    (socleExponents M.ideal).ncard ≤ (minimalExponents M.ideal).ncard +
      (fullSupportGenerators M.ideal).ncard - 2 := by
  have htag := Staircase.socle_count_le_tags M.ideal
  have homit := Staircase.main_count_add_two_le M
  omega

/-- Support-refined type bound for every proper Artinian monomial ideal in three variables. -/
theorem support_refined_monomial_type_bound (M : ArtinianMonomial k) :
    quotientType M.ideal ≤ mu M.ideal + q_fs M.ideal - 2 :=
  (support_refined_iff_staircase_count M.ideal M.monomial).mpr (staircase_corner_bound M)

end NS25Lean.L3A
