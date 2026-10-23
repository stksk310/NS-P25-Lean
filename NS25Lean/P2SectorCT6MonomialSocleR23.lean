import NS25Lean.P2SectorCT5FiniteCountingR22

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
noncomputable section
namespace NS25Lean.L5A2C4OR23
open L5A2C4OR20 L5A2C4OR21

def PolynomialMinimal (G : Set Monomial) (z : Monomial) : Prop :=
  z ∈ monomialClosure G ∧ ∀ w ∈ monomialClosure G,
    w.1 ≤ z.1 → w.2.1 ≤ z.2.1 → w.2.2 ≤ z.2.2 → w = z

def MonomialSocle (G : Set Monomial) (z : Monomial) : Prop :=
  z ∉ monomialClosure G ∧
    (z.1+1,z.2.1,z.2.2) ∈ monomialClosure G ∧
    (z.1,z.2.1+1,z.2.2) ∈ monomialClosure G ∧
    (z.1,z.2.1,z.2.2+1) ∈ monomialClosure G

abbrev Cell := ℕ × ℕ

def StandardSlice (G : Set Monomial) (k : ℕ) : Set Cell :=
  {p | (k,p.1,p.2) ∉ monomialClosure G}

def SliceCorner (D : Set Cell) (p : Cell) : Prop :=
  p ∈ D ∧ (p.1+1,p.2) ∉ D ∧ (p.1,p.2+1) ∉ D

def DownwardClosed (D : Set Cell) : Prop :=
  ∀ p ∈ D, ∀ q : Cell, q.1 ≤ p.1 → q.2 ≤ p.2 → q ∈ D

theorem polynomialMinimal_mem_generator (G : Set Monomial) (z : Monomial)
    (hz : PolynomialMinimal G z) : z ∈ G := by
  obtain ⟨g,hg,hr,hi,hj⟩ := hz.1
  have hgz := hz.2 g ⟨g,hg,le_rfl,le_rfl,le_rfl⟩ hr hi hj
  exact hgz ▸ hg

theorem polynomialMinimal_finite (G : Finset Monomial) :
    {z | PolynomialMinimal (G : Set Monomial) z}.Finite := by
  exact G.finite_toSet.subset (fun z hz => polynomialMinimal_mem_generator _ _ hz)

/-- A true coordinatewise minimal divisor, selected by the natural sum rank. -/
theorem monomialClosure_minimal_divisor (G : Set Monomial) (z : Monomial)
    (hz : z ∈ monomialClosure G) :
    ∃ w, PolynomialMinimal G w ∧ w.1 ≤ z.1 ∧ w.2.1 ≤ z.2.1 ∧ w.2.2 ≤ z.2.2 := by
  classical
  let P : ℕ → Prop := fun n => ∃ w ∈ monomialClosure G,
    w.1 ≤ z.1 ∧ w.2.1 ≤ z.2.1 ∧ w.2.2 ≤ z.2.2 ∧ w.1+w.2.1+w.2.2=n
  have hex : ∃ n, P n := ⟨_,z,hz,le_rfl,le_rfl,le_rfl,rfl⟩
  obtain ⟨w,hw,hr,hi,hj,hs⟩ := Nat.find_spec hex
  refine ⟨w,⟨hw,?_⟩,hr,hi,hj⟩
  intro v hv hvr hvi hvj
  have hsum := Nat.find_min' hex
    (show P (v.1+v.2.1+v.2.2) from
      ⟨v,hv,hvr.trans hr,hvi.trans hi,hvj.trans hj,rfl⟩)
  have h1 : v.1=w.1 := by omega
  have h2 : v.2.1=w.2.1 := by omega
  have h3 : v.2.2=w.2.2 := by omega
  exact Prod.ext h1 (Prod.ext h2 h3)

def minimalGenerators (G : Finset Monomial) : Finset Monomial := by
  classical
  exact G.filter (PolynomialMinimal (G : Set Monomial))

theorem mem_minimalGenerators (G : Finset Monomial) (z : Monomial) :
    z ∈ minimalGenerators G ↔ PolynomialMinimal (G : Set Monomial) z := by
  classical
  simp only [minimalGenerators,Finset.mem_filter]
  exact ⟨fun h => h.2,fun h => ⟨polynomialMinimal_mem_generator _ _ h,h⟩⟩

/-- Redundant listed generators are removed without changing the ideal. -/
theorem closure_minimalGenerators_eq (G : Finset Monomial) :
    monomialClosure (minimalGenerators G : Set Monomial) = monomialClosure (G : Set Monomial) := by
  ext z
  constructor
  · rintro ⟨w,hw,hr,hi,hj⟩
    exact monomialClosure_upward ((mem_minimalGenerators G w).mp hw).1 hr hi hj
  · intro hz
    obtain ⟨w,hw,hr,hi,hj⟩ := monomialClosure_minimal_divisor _ z hz
    exact ⟨w,(mem_minimalGenerators G w).mpr hw,hr,hi,hj⟩

theorem pureX_minimum_exists_unique (G : Set Monomial)
    (hproper : (0,0,0) ∉ monomialClosure G) (a : ℕ)
    (ha : (a,0,0) ∈ monomialClosure G) :
    ∃! n : ℕ, 0<n ∧ PolynomialMinimal G (n,0,0) := by
  obtain ⟨w,hw,hr,hi,hj⟩ := monomialClosure_minimal_divisor G (a,0,0) ha
  have hwi : w.2.1=0 := by simp only [Prod.fst,Prod.snd] at hi; omega
  have hwj : w.2.2=0 := by simp only [Prod.fst,Prod.snd] at hj; omega
  have heq : w=(w.1,0,0) := Prod.ext rfl (Prod.ext hwi hwj)
  have hmin : PolynomialMinimal G (w.1,0,0) := heq ▸ hw
  have hpos : 0<w.1 := by
    by_contra h
    have hz : w.1=0 := by omega
    exact hproper (hz ▸ hmin.1)
  refine ⟨w.1,⟨hpos,hmin⟩,?_⟩
  intro n hn
  rcases le_total n w.1 with hle | hle
  · exact congrArg Prod.fst (hmin.2 _ hn.2.1 hle le_rfl le_rfl)
  · exact (congrArg Prod.fst (hn.2.2 _ hmin.1 hle le_rfl le_rfl)).symm

theorem pureY_minimum_exists_unique (G : Set Monomial)
    (hproper : (0,0,0) ∉ monomialClosure G) (b : ℕ)
    (hb : (0,b,0) ∈ monomialClosure G) :
    ∃! n : ℕ, 0<n ∧ PolynomialMinimal G (0,n,0) := by
  obtain ⟨w,hw,hr,hi,hj⟩ := monomialClosure_minimal_divisor G (0,b,0) hb
  have hwr : w.1=0 := by simp only [Prod.fst,Prod.snd] at hr; omega
  have hwj : w.2.2=0 := by simp only [Prod.fst,Prod.snd] at hj; omega
  have heq : w=(0,w.2.1,0) := Prod.ext hwr (Prod.ext rfl hwj)
  have hmin : PolynomialMinimal G (0,w.2.1,0) := heq ▸ hw
  have hpos : 0<w.2.1 := by
    by_contra h
    have hz : w.2.1=0 := by omega
    exact hproper (hz ▸ hmin.1)
  refine ⟨w.2.1,⟨hpos,hmin⟩,?_⟩
  intro n hn
  rcases le_total n w.2.1 with hle | hle
  · exact congrArg (fun z : Monomial => z.2.1) (hmin.2 _ hn.2.1 le_rfl hle le_rfl)
  · exact (congrArg (fun z : Monomial => z.2.1) (hn.2.2 _ hmin.1 le_rfl hle le_rfl)).symm

theorem pureZ_minimum_exists_unique (G : Set Monomial)
    (hproper : (0,0,0) ∉ monomialClosure G) (c : ℕ)
    (hc : (0,0,c) ∈ monomialClosure G) :
    ∃! n : ℕ, 0<n ∧ PolynomialMinimal G (0,0,n) := by
  obtain ⟨w,hw,hr,hi,hj⟩ := monomialClosure_minimal_divisor G (0,0,c) hc
  have hwr : w.1=0 := by simp only [Prod.fst,Prod.snd] at hr; omega
  have hwi : w.2.1=0 := by simp only [Prod.fst,Prod.snd] at hi; omega
  have heq : w=(0,0,w.2.2) := Prod.ext hwr (Prod.ext hwi rfl)
  have hmin : PolynomialMinimal G (0,0,w.2.2) := heq ▸ hw
  have hpos : 0<w.2.2 := by
    by_contra h
    have hz : w.2.2=0 := by omega
    exact hproper (hz ▸ hmin.1)
  refine ⟨w.2.2,⟨hpos,hmin⟩,?_⟩
  intro n hn
  rcases le_total n w.2.2 with hle | hle
  · exact congrArg (fun z : Monomial => z.2.2) (hmin.2 _ hn.2.1 le_rfl le_rfl hle)
  · exact (congrArg (fun z : Monomial => z.2.2) (hn.2.2 _ hmin.1 le_rfl le_rfl hle)).symm

theorem minimal_support_exhaustive (G : Set Monomial)
    (hproper : (0,0,0) ∉ monomialClosure G) (z : Monomial)
    (hz : PolynomialMinimal G z) :
    (0<z.1 ∧ z.2.1=0 ∧ z.2.2=0) ∨
    (z.1=0 ∧ 0<z.2.1 ∧ z.2.2=0) ∨
    (z.1=0 ∧ z.2.1=0 ∧ 0<z.2.2) ∨
    (0<z.1 ∧ 0<z.2.1 ∧ z.2.2=0) ∨
    (0<z.1 ∧ z.2.1=0 ∧ 0<z.2.2) ∨
    (z.1=0 ∧ 0<z.2.1 ∧ 0<z.2.2) ∨
    (0<z.1 ∧ 0<z.2.1 ∧ 0<z.2.2) := by
  have hnonzero : ¬ (z.1=0 ∧ z.2.1=0 ∧ z.2.2=0) := by
    rintro ⟨hr,hi,hj⟩
    have heq : z=(0,0,0) := Prod.ext hr (Prod.ext hi hj)
    exact hproper (heq ▸ hz.1)
  omega

theorem standardSlice_downwardClosed (G : Set Monomial) (k : ℕ) :
    DownwardClosed (StandardSlice G k) := by
  intro p hp q h1 h2 hq
  exact hp (monomialClosure_upward hq le_rfl h1 h2)

theorem standardSlice_antitone (G : Set Monomial) (k l : ℕ) (hkl : k ≤ l) :
    StandardSlice G l ⊆ StandardSlice G k := by
  intro p hp hq
  exact hp (monomialClosure_upward hq hkl le_rfl le_rfl)

theorem socle_iff_sliceCorner_dies (G : Set Monomial) (k i j : ℕ) :
    MonomialSocle G (k,i,j) ↔
      SliceCorner (StandardSlice G k) (i,j) ∧ (i,j) ∉ StandardSlice G (k+1) := by
  simp only [MonomialSocle,SliceCorner,StandardSlice,Set.mem_ofPred_eq,Prod.fst,Prod.snd,
    not_not]
  tauto

theorem sliceCorner_survives (D E : Set Cell) (hsub : E ⊆ D) (p : Cell)
    (hc : SliceCorner D p) (hp : p ∈ E) : SliceCorner E p := by
  exact ⟨hp,fun h => hc.2.1 (hsub h),fun h => hc.2.2 (hsub h)⟩

theorem standardMonomials_box (G : Set Monomial) (a b c : ℕ)
    (ha : (a,0,0) ∈ monomialClosure G)
    (hb : (0,b,0) ∈ monomialClosure G)
    (hc : (0,0,c) ∈ monomialClosure G) (z : Monomial)
    (hz : z ∉ monomialClosure G) : z.1 < a ∧ z.2.1 < b ∧ z.2.2 < c := by
  constructor
  · by_contra h; exact hz (monomialClosure_upward ha (by omega) (Nat.zero_le _) (Nat.zero_le _))
  constructor
  · by_contra h; exact hz (monomialClosure_upward hb (Nat.zero_le _) (by simp only [Prod.fst,Prod.snd]; omega) (Nat.zero_le _))
  · by_contra h; exact hz (monomialClosure_upward hc (Nat.zero_le _) (Nat.zero_le _) (by simp only [Prod.fst,Prod.snd]; omega))

theorem standardMonomials_finite (G : Set Monomial) (a b c : ℕ)
    (ha : (a,0,0) ∈ monomialClosure G)
    (hb : (0,b,0) ∈ monomialClosure G)
    (hc : (0,0,c) ∈ monomialClosure G) :
    {z | z ∉ monomialClosure G}.Finite := by
  apply (Set.finite_Iic (a,b,c)).subset
  intro z hz
  have h := standardMonomials_box G a b c ha hb hc z hz
  exact ⟨h.1.le,h.2.1.le,h.2.2.le⟩

theorem monomialSocle_finite (G : Set Monomial) (a b c : ℕ)
    (ha : (a,0,0) ∈ monomialClosure G)
    (hb : (0,b,0) ∈ monomialClosure G)
    (hc : (0,0,c) ∈ monomialClosure G) :
    {z | MonomialSocle G z}.Finite :=
  (standardMonomials_finite G a b c ha hb hc).subset (fun _ hz => hz.1)

theorem standardSlice_finite (G : Set Monomial) (k b c : ℕ)
    (hb : (0,b,0) ∈ monomialClosure G)
    (hc : (0,0,c) ∈ monomialClosure G) : (StandardSlice G k).Finite := by
  apply (Set.finite_Iic (b,c)).subset
  intro p hp
  constructor
  · by_contra h
    exact hp (monomialClosure_upward hb (Nat.zero_le _) (by simp only [Prod.fst,Prod.snd]; omega) (Nat.zero_le _))
  · by_contra h
    exact hp (monomialClosure_upward hc (Nat.zero_le _) (Nat.zero_le _) (by simp only [Prod.fst,Prod.snd]; omega))

def corners (D : Finset Cell) : Finset Cell :=
  D.filter (fun p => (p.1+1,p.2) ∉ D ∧ (p.1,p.2+1) ∉ D)

def quadrantCut (D : Finset Cell) (b c : ℕ) : Finset Cell :=
  D.filter (fun p => ¬ (b ≤ p.1 ∧ c ≤ p.2))

def newCorners (D E : Finset Cell) : Finset Cell := corners E \ corners D

theorem mem_corners (D : Finset Cell) (p : Cell) :
    p ∈ corners D ↔ SliceCorner (D : Set Cell) p := by
  simp [corners,SliceCorner]

theorem quadrantCut_subset (D : Finset Cell) (b c : ℕ) : quadrantCut D b c ⊆ D :=
  Finset.filter_subset _ _

theorem quadrantCut_downwardClosed (D : Finset Cell) (hD : DownwardClosed (D : Set Cell))
    (b c : ℕ) : DownwardClosed (quadrantCut D b c : Set Cell) := by
  intro p hp q h1 h2
  obtain ⟨hp,hcut⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hD p hp q h1 h2,?_⟩
  intro h
  exact hcut ⟨h.1.trans h1,h.2.trans h2⟩

/-- Every newly exposed corner lies on one of the two actual cut boundaries. -/
theorem quadrant_newCorner_boundary (D : Finset Cell) (b c : ℕ) (p : Cell)
    (hp : p ∈ newCorners D (quadrantCut D b c)) :
    p.1+1=b ∨ p.2+1=c := by
  obtain ⟨hp,hnot⟩ := Finset.mem_sdiff.mp hp
  have hs := (mem_corners _ _).mp hp
  have hmem := Finset.mem_filter.mp hs.1
  have hne : ¬ ((p.1+1,p.2) ∉ D ∧ (p.1,p.2+1) ∉ D) := by
    intro h
    exact hnot ((mem_corners _ _).mpr ⟨hmem.1,h⟩)
  by_cases h1 : (p.1+1,p.2) ∈ D
  · have hcut : b ≤ p.1+1 ∧ c ≤ p.2 := by
      by_contra h
      exact hs.2.1 (Finset.mem_filter.mpr ⟨h1,h⟩)
    left
    have := hmem.2
    omega
  · have h2 : (p.1,p.2+1) ∈ D := by tauto
    have hcut : b ≤ p.1 ∧ c ≤ p.2+1 := by
      by_contra h
      exact hs.2.2 (Finset.mem_filter.mpr ⟨h2,h⟩)
    right
    have := hmem.2
    omega

theorem corner_same_first_unique (D : Finset Cell) (hD : DownwardClosed (D : Set Cell))
    (p q : Cell) (hp : p ∈ corners D) (hq : q ∈ corners D) (h : p.1=q.1) : p=q := by
  have hpc := (mem_corners _ _).mp hp
  have hqc := (mem_corners _ _).mp hq
  have heq : p.2=q.2 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact hpc.2.2 (hD q hqc.1 (p.1,p.2+1) (by simp [h]) (by simp; omega))
    · exact hqc.2.2 (hD p hpc.1 (q.1,q.2+1) (by simp [h]) (by simp; omega))
  exact Prod.ext h heq

theorem corner_same_second_unique (D : Finset Cell) (hD : DownwardClosed (D : Set Cell))
    (p q : Cell) (hp : p ∈ corners D) (hq : q ∈ corners D) (h : p.2=q.2) : p=q := by
  have hpc := (mem_corners _ _).mp hp
  have hqc := (mem_corners _ _).mp hq
  have heq : p.1=q.1 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact hpc.2.1 (hD q hqc.1 (p.1+1,p.2) (by simp; omega) (by simp [h]))
    · exact hqc.2.1 (hD p hpc.1 (q.1+1,q.2) (by simp; omega) (by simp [h]))
  exact Prod.ext heq h

theorem quadrant_newCorner_card_le_two (D : Finset Cell)
    (hD : DownwardClosed (D : Set Cell)) (b c : ℕ) :
    (newCorners D (quadrantCut D b c)).card ≤ 2 := by
  let N := newCorners D (quadrantCut D b c)
  let V := N.filter (fun p => p.1+1=b)
  let W := N.filter (fun p => p.2+1=c)
  have hsub : N ⊆ V ∪ W := by
    intro p hp
    rcases quadrant_newCorner_boundary D b c p hp with hv | hw
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hv⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hw⟩)
  have hv : V.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hp,hpb⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq,hqb⟩ := Finset.mem_filter.mp hq
    exact corner_same_first_unique _ (quadrantCut_downwardClosed D hD b c) p q
      (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hq).1 (by omega)
  have hw : W.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hp,hpc⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq,hqc⟩ := Finset.mem_filter.mp hq
    exact corner_same_second_unique _ (quadrantCut_downwardClosed D hD b c) p q
      (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hq).1 (by omega)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le V W)
  change N.card ≤ 2
  omega

theorem strip_newCorner_card_le_one (D : Finset Cell)
    (hD : DownwardClosed (D : Set Cell)) (b : ℕ) :
    (newCorners D (quadrantCut D b 0)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hpb := quadrant_newCorner_boundary D b 0 p hp
  have hqb := quadrant_newCorner_boundary D b 0 q hq
  exact corner_same_first_unique _ (quadrantCut_downwardClosed D hD b 0) p q
    (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hq).1 (by omega)

theorem horizontalStrip_newCorner_card_le_one (D : Finset Cell)
    (hD : DownwardClosed (D : Set Cell)) (c : ℕ) :
    (newCorners D (quadrantCut D 0 c)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hpc := quadrant_newCorner_boundary D 0 c p hp
  have hqc := quadrant_newCorner_boundary D 0 c q hq
  exact corner_same_second_unique _ (quadrantCut_downwardClosed D hD 0 c) p q
    (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hq).1 (by omega)

theorem pureX_cut_empty (D : Finset Cell) : quadrantCut D 0 0 = ∅ := by
  simp [quadrantCut]

theorem cornerStep_balance (D E : Finset Cell) :
    (corners D \ corners E).card + (corners E).card =
      (newCorners D E).card + (corners D).card := by
  have h1 := Finset.card_sdiff_add_card_inter (corners D) (corners E)
  have h2 := Finset.card_sdiff_add_card_inter (corners E) (corners D)
  rw [Finset.inter_comm] at h2
  unfold newCorners
  omega

theorem cornerDeaths_eq_deleted (D E : Finset Cell) (hsub : E ⊆ D) :
    corners D \ corners E = (corners D).filter (fun p => p ∉ E) := by
  ext p
  simp only [Finset.mem_sdiff,Finset.mem_filter]
  constructor
  · rintro ⟨hp,hne⟩
    refine ⟨hp,?_⟩
    intro he
    exact hne ((mem_corners _ _).mpr
      (sliceCorner_survives (D : Set Cell) (E : Set Cell) hsub p
        ((mem_corners _ _).mp hp) he))
  · rintro ⟨hp,hne⟩
    exact ⟨hp,fun he => hne ((mem_corners _ _).mp he).1⟩

/-- Exact finite birth/death balance; no distinct-level or genericity hypothesis. -/
theorem cornerLedger_balance (D : ℕ → Finset Cell) (n : ℕ) :
    (∑ k ∈ Finset.range n, (corners (D k) \ corners (D (k+1))).card) +
      (corners (D n)).card =
    (corners (D 0)).card +
      ∑ k ∈ Finset.range n, (newCorners (D k) (D (k+1))).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have hs := cornerStep_balance (D n) (D (n+1))
    omega

/-- Complete deletion bounds total deaths by initial corners plus all births. -/
theorem cornerLedger_death_bound (D : ℕ → Finset Cell) (n : ℕ) :
    (∑ k ∈ Finset.range n, (corners (D k) \ corners (D (k+1))).card) ≤
      (corners (D 0)).card +
        ∑ k ∈ Finset.range n, (newCorners (D k) (D (k+1))).card := by
  have h := cornerLedger_balance D n
  omega

def applyCuts (D : Finset Cell) : List Cell → Finset Cell
  | [] => D
  | p :: ps => applyCuts (quadrantCut D p.1 p.2) ps

def cutDeaths (D : Finset Cell) : List Cell → ℕ
  | [] => 0
  | p :: ps => (corners D \ corners (quadrantCut D p.1 p.2)).card +
      cutDeaths (quadrantCut D p.1 p.2) ps

def cutBirths (D : Finset Cell) : List Cell → ℕ
  | [] => 0
  | p :: ps => (newCorners D (quadrantCut D p.1 p.2)).card +
      cutBirths (quadrantCut D p.1 p.2) ps

def cutCost (p : Cell) : ℕ := (if 0<p.1 then 1 else 0) + (if 0<p.2 then 1 else 0)

theorem quadrant_newCorner_card_le_cost (D : Finset Cell)
    (hD : DownwardClosed (D : Set Cell)) (p : Cell) :
    (newCorners D (quadrantCut D p.1 p.2)).card ≤ cutCost p := by
  by_cases hb : p.1=0
  · by_cases hc : p.2=0
    · simp [hb,hc,pureX_cut_empty,newCorners,corners,cutCost]
    · have h := horizontalStrip_newCorner_card_le_one D hD p.2
      simpa [cutCost,hb,hc,Nat.pos_iff_ne_zero] using h
  · by_cases hc : p.2=0
    · have h := strip_newCorner_card_le_one D hD p.1
      simpa [cutCost,hb,hc,Nat.pos_iff_ne_zero] using h
    · have h := quadrant_newCorner_card_le_two D hD p.1 p.2
      simpa [cutCost,hb,hc,Nat.pos_iff_ne_zero] using h

/-- Literal sequential cuts; same-level cuts are allowed and never discarded. -/
theorem sequentialCuts_balance (ps : List Cell) (D : Finset Cell) :
    cutDeaths D ps + (corners (applyCuts D ps)).card =
      (corners D).card + cutBirths D ps := by
  induction ps generalizing D with
  | nil => simp [cutDeaths,cutBirths,applyCuts]
  | cons p ps ih =>
    simp only [cutDeaths,cutBirths,applyCuts]
    have hs := cornerStep_balance D (quadrantCut D p.1 p.2)
    have ht := ih (quadrantCut D p.1 p.2)
    omega

theorem sequentialCuts_birth_bound (ps : List Cell) (D : Finset Cell)
    (hD : DownwardClosed (D : Set Cell)) :
    cutBirths D ps ≤ (ps.map cutCost).sum := by
  induction ps generalizing D with
  | nil => simp [cutBirths]
  | cons p ps ih =>
    simp only [cutBirths,List.map_cons,List.sum_cons]
    exact Nat.add_le_add (quadrant_newCorner_card_le_cost D hD p)
      (ih _ (quadrantCut_downwardClosed D hD p.1 p.2))

theorem sequentialCuts_death_bound (ps : List Cell) (D : Finset Cell)
    (hD : DownwardClosed (D : Set Cell)) :
    cutDeaths D ps ≤ (corners D).card + (ps.map cutCost).sum := by
  have hb := sequentialCuts_birth_bound ps D hD
  have he := sequentialCuts_balance ps D
  omega

theorem sequentialCuts_subset (ps : List Cell) (D : Finset Cell) : applyCuts D ps ⊆ D := by
  induction ps generalizing D with
  | nil => exact fun _ h => h
  | cons p ps ih =>
    exact (ih _).trans (quadrantCut_subset D p.1 p.2)

theorem sequentialCuts_downwardClosed (ps : List Cell) (D : Finset Cell)
    (hD : DownwardClosed (D : Set Cell)) : DownwardClosed (applyCuts D ps : Set Cell) := by
  induction ps generalizing D with
  | nil => exact hD
  | cons p ps ih => exact ih _ (quadrantCut_downwardClosed D hD p.1 p.2)

theorem exists_corner_above (D : Finset Cell) (p : Cell) (hp : p ∈ D) :
    ∃ q ∈ corners D, p.1 ≤ q.1 ∧ p.2 ≤ q.2 := by
  let A := D.filter (fun q => p.1 ≤ q.1 ∧ p.2 ≤ q.2)
  have hA : A.Nonempty := ⟨p,Finset.mem_filter.mpr ⟨hp,le_rfl,le_rfl⟩⟩
  obtain ⟨q,hq,hmax⟩ := Finset.exists_max_image A (fun q => q.1+q.2) hA
  obtain ⟨hqD,h1,h2⟩ := Finset.mem_filter.mp hq
  refine ⟨q,(mem_corners _ _).mpr ⟨hqD,?_,?_⟩,h1,h2⟩
  · intro hs
    have hsu : (q.1+1,q.2) ∈ A := Finset.mem_filter.mpr ⟨hs,by simp; omega,h2⟩
    have hm := hmax _ hsu
    simp only [Prod.fst,Prod.snd] at hm
    omega
  · intro hs
    have hsu : (q.1,q.2+1) ∈ A := Finset.mem_filter.mpr ⟨hs,h1,by simp; omega⟩
    have hm := hmax _ hsu
    simp only [Prod.fst,Prod.snd] at hm
    omega

theorem quadrant_birth_implies_death (D : Finset Cell) (b c : ℕ)
    (hn : (newCorners D (quadrantCut D b c)).Nonempty) :
    (corners D \ corners (quadrantCut D b c)).Nonempty := by
  obtain ⟨p,hp⟩ := hn
  obtain ⟨hpc,hpn⟩ := Finset.mem_sdiff.mp hp
  have hpD := (Finset.mem_filter.mp ((mem_corners _ _).mp hpc).1).1
  have hs : (p.1+1,p.2) ∈ D ∨ (p.1,p.2+1) ∈ D := by
    by_contra h
    apply hpn
    apply (mem_corners _ _).mpr
    exact ⟨hpD,by tauto,by tauto⟩
  have hcutCorner := (mem_corners _ _).mp hpc
  have hdeleted : ∃ z ∈ D, b ≤ z.1 ∧ c ≤ z.2 := by
    rcases hs with hs | hs
    · refine ⟨(p.1+1,p.2),hs,?_⟩
      by_contra h
      exact hcutCorner.2.1 (Finset.mem_filter.mpr ⟨hs,h⟩)
    · refine ⟨(p.1,p.2+1),hs,?_⟩
      by_contra h
      exact hcutCorner.2.2 (Finset.mem_filter.mpr ⟨hs,h⟩)
  obtain ⟨z,hz,hb,hc⟩ := hdeleted
  obtain ⟨q,hq,h1,h2⟩ := exists_corner_above D z hz
  refine ⟨q,Finset.mem_sdiff.mpr ⟨hq,?_⟩⟩
  intro hqE
  have hno := (Finset.mem_filter.mp ((mem_corners _ _).mp hqE).1).2
  exact hno ⟨hb.trans h1,hc.trans h2⟩

/-- Net corner growth is at most one: a nonempty birth forces a genuine death. -/
theorem quadrant_corner_growth_le_one (D : Finset Cell)
    (hD : DownwardClosed (D : Set Cell)) (b c : ℕ) :
    (corners (quadrantCut D b c)).card ≤ (corners D).card+1 := by
  have hs := cornerStep_balance D (quadrantCut D b c)
  have hb := quadrant_newCorner_card_le_two D hD b c
  by_cases hn : (newCorners D (quadrantCut D b c)).Nonempty
  · have hd := Finset.card_pos.mpr (quadrant_birth_implies_death D b c hn)
    omega
  · have hz : (newCorners D (quadrantCut D b c)).card=0 := by
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
    omega

theorem sequentialCuts_corner_growth (ps : List Cell) (D : Finset Cell)
    (hD : DownwardClosed (D : Set Cell)) :
    (corners (applyCuts D ps)).card ≤ (corners D).card+ps.length := by
  induction ps generalizing D with
  | nil => simp [applyCuts]
  | cons p ps ih =>
    have hs := quadrant_corner_growth_le_one D hD p.1 p.2
    have ht := ih _ (quadrantCut_downwardClosed D hD p.1 p.2)
    simp only [applyCuts,List.length_cons]
    omega

/-- Batch deaths inject into intermediate deaths, irrespective of tied levels. -/
theorem sequentialCuts_batch_deaths_le (ps : List Cell) (D : Finset Cell) :
    (corners D \ corners (applyCuts D ps)).card ≤ cutDeaths D ps := by
  induction ps generalizing D with
  | nil => simp [applyCuts,cutDeaths]
  | cons p ps ih =>
    let E := quadrantCut D p.1 p.2
    have hsub : corners D \ corners (applyCuts E ps) ⊆
        (corners D \ corners E) ∪ (corners E \ corners (applyCuts E ps)) := by
      intro z hz
      obtain ⟨hz,hn⟩ := Finset.mem_sdiff.mp hz
      by_cases he : z ∈ corners E
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he,hn⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz,he⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have ht := ih E
    change (corners D \ corners (applyCuts E ps)).card ≤
      (corners D \ corners E).card + cutDeaths E ps
    omega

def rectangle (b c : ℕ) : Finset Cell := (Finset.range b).product (Finset.range c)

theorem rectangle_downwardClosed (b c : ℕ) : DownwardClosed (rectangle b c : Set Cell) := by
  intro p hp q h1 h2
  simp only [rectangle,Finset.product_eq_sprod,Finset.mem_coe,Finset.mem_product,Finset.mem_range] at hp ⊢
  exact ⟨h1.trans_lt hp.1,h2.trans_lt hp.2⟩

theorem rectangle_corners (b c : ℕ) (hb : 0<b) (hc : 0<c) :
    corners (rectangle b c) = {(b-1,c-1)} := by
  ext p
  rcases p with ⟨i,j⟩
  simp only [corners,rectangle,Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product,Finset.mem_range,
    Finset.mem_singleton,Prod.mk.injEq,Prod.fst,Prod.snd]
  omega

theorem applyCuts_mem_iff (ps : List Cell) (D : Finset Cell) (p : Cell) :
    p ∈ applyCuts D ps ↔ p ∈ D ∧ ∀ q ∈ ps, ¬ (q.1 ≤ p.1 ∧ q.2 ≤ p.2) := by
  induction ps generalizing D with
  | nil => simp [applyCuts]
  | cons q ps ih =>
    simp only [applyCuts,ih,quadrantCut,Finset.mem_filter,List.mem_cons]
    constructor
    · rintro ⟨⟨hp,hq⟩,hps⟩
      refine ⟨hp,?_⟩
      intro r hr
      rcases hr with rfl | hr
      · exact hq
      · exact hps r hr
    · rintro ⟨hp,hps⟩
      exact ⟨⟨hp,hps q (Or.inl rfl)⟩,fun r hr => hps r (Or.inr hr)⟩

def yzGenerators (G : Finset Monomial) : Finset Monomial := by
  classical
  exact (minimalGenerators G).filter (fun z => z.1=0 ∧ 0<z.2.1 ∧ 0<z.2.2)

def yzCuts (G : Finset Monomial) : List Cell := (yzGenerators G).toList.map Prod.snd

theorem initialSlice_eq_cuts (G : Finset Monomial)
    (b c : ℕ)
    (hb : PolynomialMinimal (G : Set Monomial) (0,b,0))
    (hc : PolynomialMinimal (G : Set Monomial) (0,0,c)) :
    StandardSlice (G : Set Monomial) 0 = (applyCuts (rectangle b c) (yzCuts G) : Set Cell) := by
  classical
  ext p
  rw [Finset.mem_coe,applyCuts_mem_iff]
  constructor
  · intro hp
    refine ⟨?_,?_⟩
    · simp only [rectangle,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range]
      constructor
      · by_contra h
        exact hp (monomialClosure_upward hb.1 le_rfl (by simp only [Prod.fst,Prod.snd]; omega) (Nat.zero_le _))
      · by_contra h
        exact hp (monomialClosure_upward hc.1 le_rfl (Nat.zero_le _) (by simp only [Prod.fst,Prod.snd]; omega))
    · intro q hq hdiv
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hq
      have hg' := Finset.mem_filter.mp (Finset.mem_toList.mp hg)
      have hmin := (mem_minimalGenerators G g).mp hg'.1
      exact hp (monomialClosure_upward hmin.1 (by simp only [Prod.fst]; omega) hdiv.1 hdiv.2)
  · rintro ⟨hp,hcuts⟩ hcl
    have hrect := hp
    simp only [rectangle,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] at hrect
    obtain ⟨g,hg,hr,hi,hj⟩ := monomialClosure_minimal_divisor _ (0,p.1,p.2) hcl
    simp only [Prod.fst,Prod.snd] at hr hi hj
    have hgr : g.1=0 := by omega
    by_cases hgi : g.2.1=0
    · have heq : g=(0,0,g.2.2) := Prod.ext hgr (Prod.ext hgi rfl)
      have hle : g.2.2 ≤ c := by omega
      have he := hc.2 g hg.1 (by simp [hgr]) (by simp [hgi]) hle
      have hjc := congrArg (fun z : Monomial => z.2.2) he
      simp only [Prod.fst,Prod.snd] at hj hjc
      omega
    · by_cases hgj : g.2.2=0
      · have hle : g.2.1 ≤ b := by omega
        have he := hb.2 g hg.1 (by simp [hgr]) hle (by simp [hgj])
        have hib := congrArg (fun z : Monomial => z.2.1) he
        simp only [Prod.fst,Prod.snd] at hi hib
        omega
      · have hmem : g ∈ yzGenerators G := Finset.mem_filter.mpr
          ⟨(mem_minimalGenerators G g).mpr hg,hgr,by omega,by omega⟩
        have hcut : g.2 ∈ yzCuts G := List.mem_map.mpr ⟨g,Finset.mem_toList.mpr hmem,rfl⟩
        exact hcuts g.2 hcut ⟨hi,hj⟩

/-- Initial yz-plane bound uses TRUE polynomial minima, not the listed generators. -/
theorem initialCuts_corner_bound (G : Finset Monomial) (b c : ℕ)
    (hbpos : 0<b) (hcpos : 0<c) :
    (corners (applyCuts (rectangle b c) (yzCuts G))).card ≤ 1+(yzGenerators G).card := by
  have h := sequentialCuts_corner_growth (yzCuts G) (rectangle b c)
    (rectangle_downwardClosed b c)
  rw [rectangle_corners b c hbpos hcpos] at h
  simpa [yzCuts] using h

theorem initialSlice_corner_bound (G : Finset Monomial) (b c : ℕ)
    (hbpos : 0<b) (hcpos : 0<c)
    (hb : PolynomialMinimal (G : Set Monomial) (0,b,0))
    (hc : PolynomialMinimal (G : Set Monomial) (0,0,c)) :
    (corners (standardSlice_finite (G : Set Monomial) 0 b c hb.1 hc.1).toFinset).card ≤
      1+(yzGenerators G).card := by
  have he : (standardSlice_finite (G : Set Monomial) 0 b c hb.1 hc.1).toFinset =
      applyCuts (rectangle b c) (yzCuts G) := by
    ext p
    rw [Set.Finite.mem_toFinset]
    exact Set.ext_iff.mp (initialSlice_eq_cuts G b c hb hc) p
  rw [he]
  exact initialCuts_corner_bound G b c hbpos hcpos

end NS25Lean.L5A2C4OR23
