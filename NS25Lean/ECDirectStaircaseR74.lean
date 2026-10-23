import NS25Lean.StaircaseCornerBound

set_option autoImplicit false
noncomputable section
namespace NS25Lean.EC.R74
open L3A L3A.Staircase

/-- An intermediate finite certificate, not a definition of historical NEIT. -/
def TagSaturation (I : Ideal (L3A.Polynomial ℚ)) : Prop :=
  (mainGenerators I).ncard + 2 = (minimalExponents I).ncard ∧
    Function.Surjective (tag I)

theorem tag_card_eq_iff_surjective (M : ArtinianMonomial ℚ) :
    (socleExponents M.ideal).ncard =
      (mainGenerators M.ideal).ncard + (fullSupportGenerators M.ideal).ncard ↔
        Function.Surjective (tag M.ideal) := by
  letI := M.artinian
  letI : Finite (socleExponents M.ideal) := (socleExponents_finite M.ideal M.monomial).to_subtype
  letI : Finite (mainGenerators M.ideal) := (mainGenerators_finite M.ideal).to_subtype
  letI : Finite (fullSupportGenerators M.ideal) := (fullSupportGenerators_finite M.ideal).to_subtype
  constructor
  · intro h
    apply ((tag_injective M.ideal).bijective_of_nat_card_le ?_).2
    simpa only [Tags,Nat.card_sum,Nat.card_coe_set_eq] using h.ge
  · intro h
    have hc := Nat.card_le_card_of_surjective (tag M.ideal) h
    have hl := socle_count_le_tags M.ideal
    have hc' : (mainGenerators M.ideal).ncard + (fullSupportGenerators M.ideal).ncard ≤
        (socleExponents M.ideal).ncard := by
      simpa only [Tags,Nat.card_sum,Nat.card_coe_set_eq] using hc
    exact le_antisymm hl hc'

def generatorGap (I : Ideal (L3A.Polynomial ℚ)) : ℤ :=
  ((minimalExponents I).ncard : ℤ) - ((mainGenerators I).ncard + 2)

def tagGap (I : Ideal (L3A.Polynomial ℚ)) : ℤ :=
  ((mainGenerators I).ncard : ℤ) + (fullSupportGenerators I).ncard - (socleExponents I).ncard

theorem generatorGap_nonneg (M : ArtinianMonomial ℚ) : 0 ≤ generatorGap M.ideal := by
  have h := main_count_add_two_le M
  unfold generatorGap
  omega

theorem tagGap_nonneg (M : ArtinianMonomial ℚ) : 0 ≤ tagGap M.ideal := by
  have h := socle_count_le_tags M.ideal
  unfold tagGap
  omega

theorem bps_gap_split (M : ArtinianMonomial ℚ) :
    (mu M.ideal : ℤ) + (q_fs M.ideal : ℤ) - 2 - (quotientType M.ideal : ℤ) =
      generatorGap M.ideal + tagGap M.ideal := by
  rw [quotientType_eq_socle_count M.ideal M.monomial,mu_eq_minimal_count M.ideal M.monomial]
  unfold generatorGap tagGap q_fs
  ring

/-- The literal direct-count objective, retaining both finite conditions. -/
theorem bps_equality_iff_tag_saturation (M : ArtinianMonomial ℚ) :
    (quotientType M.ideal + 2 = mu M.ideal + q_fs M.ideal) ↔
      ((mainGenerators M.ideal).ncard + 2 = (minimalExponents M.ideal).ncard ∧
        Function.Surjective (tag M.ideal)) := by
  rw [← tag_card_eq_iff_surjective M,quotientType_eq_socle_count M.ideal M.monomial,
    mu_eq_minimal_count M.ideal M.monomial]
  have hG := main_count_add_two_le M
  have hS := socle_count_le_tags M.ideal
  unfold q_fs
  omega

theorem bps_slack_zero_iff_tag_saturation (M : ArtinianMonomial ℚ) :
    (mu M.ideal : ℤ) + (q_fs M.ideal : ℤ) - 2 - (quotientType M.ideal : ℤ) = 0 ↔
      TagSaturation M.ideal := by
  rw [TagSaturation,← bps_equality_iff_tag_saturation M]
  omega

theorem tagGap_zero_iff_surjective (M : ArtinianMonomial ℚ) :
    tagGap M.ideal = 0 ↔ Function.Surjective (tag M.ideal) := by
  rw [← tag_card_eq_iff_surjective M]
  unfold tagGap
  omega

theorem pure_minimal_unique (I : Ideal (L3A.Polynomial ℚ)) (i : Fin 3)
    (a b : Exponent) (ha : a ∈ minimalExponents I) (hb : b ∈ minimalExponents I)
    (hao : ∀ j, j ≠ i → a j = 0) (hbo : ∀ j, j ≠ i → b j = 0) : a = b := by
  have hle (x y : Exponent) (hxy : x i ≤ y i)
      (hx : ∀ j, j ≠ i → x j = 0) : x ≤ y := by
    intro j
    by_cases hj : j = i
    · subst j; exact hxy
    · rw [hx j hj]; exact Nat.zero_le _
  rcases le_total (a i) (b i) with h | h
  · have hab := hle a b h hao
    exact le_antisymm hab (hb.2 ha.1 hab)
  · have hba := hle b a h hbo
    exact le_antisymm (ha.2 hb.1 hba) hba

/-- The omitted minimal generators are exactly the pure y and pure z ones. -/
theorem main_count_add_two_eq (M : ArtinianMonomial ℚ) :
    (mainGenerators M.ideal).ncard + 2 = (minimalExponents M.ideal).ncard := by
  classical
  obtain ⟨gy,hgy,hyp,hyo⟩ := pure_minimal M 1
  obtain ⟨gz,hgz,hzp,hzo⟩ := pure_minimal M 2
  have hy0 := hyo 0 (by decide)
  have hy2 := hyo 2 (by decide)
  have hz0 := hzo 0 (by decide)
  have hz1 := hzo 1 (by decide)
  have hyn : gy ∉ mainGenerators M.ideal := by rintro ⟨_,h | h⟩ <;> omega
  have hzn : gz ∉ mainGenerators M.ideal := by rintro ⟨_,h | h⟩ <;> omega
  have hne : gy ≠ gz := by
    intro he
    have hh := congrArg (fun g : Exponent => g 1) he
    omega
  have heq : minimalExponents M.ideal = insert gy (insert gz (mainGenerators M.ideal)) := by
    apply Set.Subset.antisymm
    · intro g hg
      by_cases hm : g ∈ mainGenerators M.ideal
      · exact Or.inr (Or.inr hm)
      have hz : g 0 = 0 := by
        by_contra hn
        exact hm ⟨hg,Or.inl (Nat.pos_of_ne_zero hn)⟩
      have haxes : g 1 = 0 ∨ g 2 = 0 := by
        by_contra! hn
        exact hm ⟨hg,Or.inr ⟨Nat.pos_of_ne_zero hn.1,Nat.pos_of_ne_zero hn.2⟩⟩
      rcases haxes with h1 | h2
      · have ho : ∀ j : Fin 3, j ≠ 2 → g j = 0 := by
          intro j hj; fin_cases j <;> simp_all
        exact Or.inr (Or.inl (pure_minimal_unique M.ideal 2 g gz hg hgz ho hzo))
      · have ho : ∀ j : Fin 3, j ≠ 1 → g j = 0 := by
          intro j hj; fin_cases j <;> simp_all
        exact Or.inl (pure_minimal_unique M.ideal 1 g gy hg hgy ho hyo)
    · intro g hg
      rcases hg with rfl | rfl | hg
      · exact hgy
      · exact hgz
      · exact hg.1
  rw [heq,Set.ncard_insert_of_notMem (by simp [hne,hyn]) ((mainGenerators_finite M.ideal).insert gz),
    Set.ncard_insert_of_notMem hzn (mainGenerators_finite M.ideal)]

theorem tag_saturation_iff_surjective (M : ArtinianMonomial ℚ) :
    TagSaturation M.ideal ↔ Function.Surjective (tag M.ideal) := by
  exact ⟨And.right,fun h => ⟨main_count_add_two_eq M,h⟩⟩

theorem bps_equality_iff_surjective (M : ArtinianMonomial ℚ) :
    quotientType M.ideal + 2 = mu M.ideal + q_fs M.ideal ↔
      Function.Surjective (tag M.ideal) := by
  rw [bps_equality_iff_tag_saturation M]
  exact tag_saturation_iff_surjective M

end NS25Lean.EC.R74
