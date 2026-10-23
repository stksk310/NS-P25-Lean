import NS25Lean.P2SectorCT6MonomialSocleR23

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NS25Lean.L5A2C4OR24
open L5A2C4OR20 L5A2C4OR21 L5A2C4OR23

theorem true_minimal_at_pureX_is_pureX (G : Set Monomial) (A : ℕ)
    (ha : PolynomialMinimal G (A,0,0)) (z : Monomial)
    (hz : PolynomialMinimal G z) (hle : A ≤ z.1) : z=(A,0,0) := by
  exact (hz.2 _ ha.1 hle (Nat.zero_le _) (Nat.zero_le _)).symm

theorem true_minimal_x_degree_le_pureX (G : Set Monomial) (A : ℕ)
    (ha : PolynomialMinimal G (A,0,0)) (z : Monomial)
    (hz : PolynomialMinimal G z) : z.1 ≤ A := by
  by_cases h : A ≤ z.1
  · rw [true_minimal_at_pureX_is_pureX G A ha z hz h]
  · omega

def xLevelGenerators (G : Finset Monomial) (q : ℕ) : Finset Monomial := by
  classical
  exact (minimalGenerators G).filter (fun z => z.1=q)

def xLevelCuts (G : Finset Monomial) (q : ℕ) : List Cell :=
  (xLevelGenerators G q).toList.map Prod.snd

theorem terminal_xLevelCuts (G : Finset Monomial) (A : ℕ)
    (ha : PolynomialMinimal (G : Set Monomial) (A,0,0)) :
    xLevelCuts G A=[(0,0)] := by
  classical
  have he : xLevelGenerators G A={(A,0,0)} := by
    ext z
    simp only [xLevelGenerators,Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨hz,hx⟩
      exact true_minimal_at_pureX_is_pureX _ A ha z
        ((mem_minimalGenerators G z).mp hz) (by omega)
    · rintro rfl
      exact ⟨(mem_minimalGenerators G _).mpr ha,rfl⟩
  simp [xLevelCuts,he]

theorem pureX_terminal_deletes (G : Finset Monomial) (A : ℕ)
    (ha : PolynomialMinimal (G : Set Monomial) (A,0,0)) (D : Finset Cell) :
    applyCuts D (xLevelCuts G A)=∅ := by
  rw [terminal_xLevelCuts G A ha]
  simp [applyCuts,pureX_cut_empty]

def sliceFinset (G : Set Monomial) (k B C : ℕ)
    (hb : (0,B,0) ∈ monomialClosure G) (hc : (0,0,C) ∈ monomialClosure G) : Finset Cell :=
  (standardSlice_finite G k B C hb hc).toFinset

theorem mem_sliceFinset (G : Set Monomial) (k B C : ℕ)
    (hb : (0,B,0) ∈ monomialClosure G) (hc : (0,0,C) ∈ monomialClosure G) (p : Cell) :
    p ∈ sliceFinset G k B C hb hc ↔ p ∈ StandardSlice G k := by
  exact Set.Finite.mem_toFinset _

theorem slice_at_pureX_empty (G : Set Monomial) (A B C : ℕ)
    (ha : (A,0,0) ∈ monomialClosure G)
    (hb : (0,B,0) ∈ monomialClosure G) (hc : (0,0,C) ∈ monomialClosure G) :
    sliceFinset G A B C hb hc=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact ((mem_sliceFinset _ _ _ _ _ _ _).mp hp)
    (monomialClosure_upward ha le_rfl (Nat.zero_le _) (Nat.zero_le _))

theorem sliceFinset_subset (G : Set Monomial) (k B C : ℕ)
    (hb : (0,B,0) ∈ monomialClosure G) (hc : (0,0,C) ∈ monomialClosure G) :
    sliceFinset G (k+1) B C hb hc ⊆ sliceFinset G k B C hb hc := by
  intro p hp
  exact (mem_sliceFinset _ _ _ _ _ _ _).mpr
    (standardSlice_antitone G k (k+1) (by omega) ((mem_sliceFinset _ _ _ _ _ _ _).mp hp))

theorem sliceFinset_downwardClosed (G : Set Monomial) (k B C : ℕ)
    (hb : (0,B,0) ∈ monomialClosure G) (hc : (0,0,C) ∈ monomialClosure G) :
    DownwardClosed (sliceFinset G k B C hb hc : Set Cell) := by
  intro p hp q h1 h2
  exact (mem_sliceFinset _ _ _ _ _ _ _).mpr
    (standardSlice_downwardClosed G k p ((mem_sliceFinset _ _ _ _ _ _ _).mp hp) q h1 h2)

theorem sliceStep_eq_levelCuts (G : Finset Monomial) (k B C : ℕ)
    (hb : (0,B,0) ∈ monomialClosure (G : Set Monomial))
    (hc : (0,0,C) ∈ monomialClosure (G : Set Monomial)) :
    sliceFinset (G : Set Monomial) (k+1) B C hb hc =
      applyCuts (sliceFinset (G : Set Monomial) k B C hb hc) (xLevelCuts G (k+1)) := by
  classical
  ext p
  rw [mem_sliceFinset,applyCuts_mem_iff,mem_sliceFinset]
  constructor
  · intro hp
    refine ⟨standardSlice_antitone _ k (k+1) (by omega) hp,?_⟩
    intro q hq hdiv
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hq
    obtain ⟨hgm,hlevel⟩ := Finset.mem_filter.mp (Finset.mem_toList.mp hg)
    exact hp (monomialClosure_upward ((mem_minimalGenerators G g).mp hgm).1
      (by simp only [Prod.fst]; omega) hdiv.1 hdiv.2)
  · rintro ⟨hp,hcuts⟩ hcl
    obtain ⟨g,hg,hr,hi,hj⟩ := monomialClosure_minimal_divisor _ (k+1,p.1,p.2) hcl
    simp only [Prod.fst,Prod.snd] at hr hi hj
    have hlevel : g.1=k+1 := by
      by_contra h
      have hle : g.1 ≤ k := by omega
      exact hp (monomialClosure_upward hg.1 hle hi hj)
    have hmem : g ∈ xLevelGenerators G (k+1) :=
      Finset.mem_filter.mpr ⟨(mem_minimalGenerators G g).mpr hg,hlevel⟩
    exact hcuts g.2 (List.mem_map.mpr ⟨g,Finset.mem_toList.mpr hmem,rfl⟩) ⟨hi,hj⟩

theorem applyCuts_append (D : Finset Cell) (ps qs : List Cell) :
    applyCuts D (ps++qs)=applyCuts (applyCuts D ps) qs := by
  induction ps generalizing D with
  | nil => rfl
  | cons p ps ih => exact ih _

theorem cutDeaths_append (D : Finset Cell) (ps qs : List Cell) :
    cutDeaths D (ps++qs)=cutDeaths D ps+cutDeaths (applyCuts D ps) qs := by
  induction ps generalizing D with
  | nil => simp [cutDeaths,applyCuts]
  | cons p ps ih => simp only [List.cons_append,cutDeaths,applyCuts,ih,Nat.add_assoc]

def allPositiveXCuts (G : Finset Monomial) : ℕ → List Cell
  | 0 => []
  | n+1 => allPositiveXCuts G n ++ xLevelCuts G (n+1)

theorem slice_eq_allCuts (G : Finset Monomial) (n B C : ℕ)
    (hb : (0,B,0) ∈ monomialClosure (G : Set Monomial))
    (hc : (0,0,C) ∈ monomialClosure (G : Set Monomial)) :
    sliceFinset (G : Set Monomial) n B C hb hc =
      applyCuts (sliceFinset (G : Set Monomial) 0 B C hb hc) (allPositiveXCuts G n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sliceStep_eq_levelCuts,ih,allPositiveXCuts,applyCuts_append]

theorem level_cutDeaths_telescope (G : Finset Monomial) (n B C : ℕ)
    (hb : (0,B,0) ∈ monomialClosure (G : Set Monomial))
    (hc : (0,0,C) ∈ monomialClosure (G : Set Monomial)) :
    (∑ k ∈ Finset.range n, cutDeaths (sliceFinset (G : Set Monomial) k B C hb hc)
      (xLevelCuts G (k+1))) =
    cutDeaths (sliceFinset (G : Set Monomial) 0 B C hb hc) (allPositiveXCuts G n) := by
  induction n with
  | zero => simp [allPositiveXCuts,cutDeaths]
  | succ n ih => rw [Finset.sum_range_succ,ih,allPositiveXCuts,cutDeaths_append,←slice_eq_allCuts]

theorem socle_x_degree_lt_pureX (G : Set Monomial) (A : ℕ)
    (ha : (A,0,0) ∈ monomialClosure G) (z : Monomial) (hz : MonomialSocle G z) : z.1<A := by
  by_contra h
  exact hz.1 (monomialClosure_upward ha (by omega) (Nat.zero_le _) (Nat.zero_le _))

def levelDeaths (G : Set Monomial) (k B C : ℕ)
    (hb : (0,B,0) ∈ monomialClosure G) (hc : (0,0,C) ∈ monomialClosure G) : Finset Cell :=
  corners (sliceFinset G k B C hb hc) \ corners (sliceFinset G (k+1) B C hb hc)

theorem mem_levelDeaths (G : Set Monomial) (k B C : ℕ)
    (hb : (0,B,0) ∈ monomialClosure G) (hc : (0,0,C) ∈ monomialClosure G) (p : Cell) :
    p ∈ levelDeaths G k B C hb hc ↔ MonomialSocle G (k,p.1,p.2) := by
  rw [levelDeaths,cornerDeaths_eq_deleted _ _ (sliceFinset_subset G k B C hb hc)]
  simp only [Finset.mem_filter,mem_corners]
  simp only [sliceFinset,Set.Finite.coe_toFinset,Set.Finite.mem_toFinset]
  exact (socle_iff_sliceCorner_dies G k p.1 p.2).symm

/-- Level is retained in the sigma tag; equal yz corners at distinct levels are distinct. -/
def socleLevelEquiv (G : Set Monomial) (A B C : ℕ)
    (ha : (A,0,0) ∈ monomialClosure G)
    (hb : (0,B,0) ∈ monomialClosure G) (hc : (0,0,C) ∈ monomialClosure G) :
    {z // MonomialSocle G z} ≃ Σ k : Fin A, ↥(levelDeaths G k.val B C hb hc) where
  toFun z := ⟨⟨z.val.1,socle_x_degree_lt_pureX G A ha z.val z.prop⟩,
    ⟨z.val.2,(mem_levelDeaths G z.val.1 B C hb hc z.val.2).mpr z.prop⟩⟩
  invFun p := ⟨(p.1.val,p.2.val.1,p.2.val.2),
    (mem_levelDeaths G p.1.val B C hb hc p.2.val).mp p.2.prop⟩
  left_inv z := by cases z; rfl
  right_inv p := by cases p; rfl

theorem socle_card_eq_level_deaths (G : Set Monomial) (A B C : ℕ)
    (ha : (A,0,0) ∈ monomialClosure G)
    (hb : (0,B,0) ∈ monomialClosure G) (hc : (0,0,C) ∈ monomialClosure G) :
    Nat.card {z // MonomialSocle G z} =
      ∑ k ∈ Finset.range A, (levelDeaths G k B C hb hc).card := by
  rw [Nat.card_congr (socleLevelEquiv G A B C ha hb hc),Nat.card_sigma]
  simp only [Nat.card_eq_finsetCard]
  exact Fin.sum_univ_eq_sum_range (fun k => (levelDeaths G k B C hb hc).card) A

theorem socle_card_le_global_cutDeaths (G : Finset Monomial) (A B C : ℕ)
    (ha : (A,0,0) ∈ monomialClosure (G : Set Monomial))
    (hb : (0,B,0) ∈ monomialClosure (G : Set Monomial))
    (hc : (0,0,C) ∈ monomialClosure (G : Set Monomial)) :
    Nat.card {z // MonomialSocle (G : Set Monomial) z} ≤
      cutDeaths (sliceFinset (G : Set Monomial) 0 B C hb hc) (allPositiveXCuts G A) := by
  rw [socle_card_eq_level_deaths _ A B C ha hb hc,←level_cutDeaths_telescope]
  apply Finset.sum_le_sum
  intro k hk
  unfold levelDeaths
  rw [sliceStep_eq_levelCuts]
  exact sequentialCuts_batch_deaths_le _ _

theorem xLevel_cutCost (G : Finset Monomial) (q : ℕ) :
    ((xLevelCuts G q).map cutCost).sum =
      ∑ g ∈ minimalGenerators G, if g.1=q then cutCost g.2 else 0 := by
  classical
  rw [xLevelCuts,List.map_map,←List.sum_toFinset _ (Finset.nodup_toList _)]
  simp only [Finset.toList_toFinset,xLevelGenerators,Finset.sum_filter,Function.comp_apply]

theorem allCuts_cost_eq_level_sum (G : Finset Monomial) (A : ℕ) :
    ((allPositiveXCuts G A).map cutCost).sum =
      ∑ k ∈ Finset.range A, ((xLevelCuts G (k+1)).map cutCost).sum := by
  induction A with
  | zero => simp [allPositiveXCuts]
  | succ A ih => simp only [allPositiveXCuts,List.map_append,List.sum_append,Finset.sum_range_succ,ih]

theorem positive_x_cutCost_eq_minimal_sum (G : Finset Monomial) (A : ℕ)
    (ha : PolynomialMinimal (G : Set Monomial) (A,0,0)) :
    ((allPositiveXCuts G A).map cutCost).sum =
      ∑ g ∈ minimalGenerators G, if 0<g.1 then cutCost g.2 else 0 := by
  classical
  rw [allCuts_cost_eq_level_sum]
  simp_rw [xLevel_cutCost]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  have hbound := true_minimal_x_degree_le_pureX _ A ha g ((mem_minimalGenerators G g).mp hg)
  by_cases hpos : 0<g.1
  · rw [ite_eq_left hpos]
    rw [Finset.sum_eq_single (g.1-1)]
    · rw [ite_eq_left (by omega)]
    · intro k hk hne
      rw [ite_eq_right (by omega)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right hpos]
    apply Finset.sum_eq_zero
    intro k hk
    exact ite_eq_right (by omega)

def xPureGenerators (G : Finset Monomial) : Finset Monomial := by
  classical
  exact (minimalGenerators G).filter (fun g => g.2.1=0 ∧ g.2.2=0)
def yPureGenerators (G : Finset Monomial) : Finset Monomial := by
  classical
  exact (minimalGenerators G).filter (fun g => g.1=0 ∧ g.2.2=0)
def zPureGenerators (G : Finset Monomial) : Finset Monomial := by
  classical
  exact (minimalGenerators G).filter (fun g => g.1=0 ∧ g.2.1=0)
def xyGenerators (G : Finset Monomial) : Finset Monomial := by
  classical
  exact (minimalGenerators G).filter (fun g => 0<g.1 ∧ 0<g.2.1 ∧ g.2.2=0)
def xzGenerators (G : Finset Monomial) : Finset Monomial := by
  classical
  exact (minimalGenerators G).filter (fun g => 0<g.1 ∧ g.2.1=0 ∧ 0<g.2.2)
def xyzGenerators (G : Finset Monomial) : Finset Monomial := by
  classical
  exact (minimalGenerators G).filter (fun g => 0<g.1 ∧ 0<g.2.1 ∧ 0<g.2.2)

theorem xPureGenerators_eq_singleton (G : Finset Monomial) (A : ℕ)
    (ha : PolynomialMinimal (G : Set Monomial) (A,0,0)) : xPureGenerators G={(A,0,0)} := by
  classical
  ext z
  simp only [xPureGenerators,Finset.mem_filter,Finset.mem_singleton]
  constructor
  · rintro ⟨hz,hi,hj⟩
    have hz' := (mem_minimalGenerators G z).mp hz
    rcases le_total z.1 A with hle | hle
    · exact ha.2 z hz'.1 hle (by simp [hi]) (by simp [hj])
    · exact true_minimal_at_pureX_is_pureX _ A ha z hz' hle
  · rintro rfl
    exact ⟨(mem_minimalGenerators G _).mpr ha,rfl,rfl⟩

theorem yPureGenerators_eq_singleton (G : Finset Monomial) (B : ℕ)
    (hb : PolynomialMinimal (G : Set Monomial) (0,B,0)) : yPureGenerators G={(0,B,0)} := by
  classical
  ext z
  simp only [yPureGenerators,Finset.mem_filter,Finset.mem_singleton]
  constructor
  · rintro ⟨hz,hr,hj⟩
    have hz' := (mem_minimalGenerators G z).mp hz
    rcases le_total z.2.1 B with hle | hle
    · exact hb.2 z hz'.1 (by simp [hr]) hle (by simp [hj])
    · exact (hz'.2 _ hb.1 (Nat.zero_le _) hle (Nat.zero_le _)).symm
  · rintro rfl
    exact ⟨(mem_minimalGenerators G _).mpr hb,rfl,rfl⟩

theorem zPureGenerators_eq_singleton (G : Finset Monomial) (C : ℕ)
    (hc : PolynomialMinimal (G : Set Monomial) (0,0,C)) : zPureGenerators G={(0,0,C)} := by
  classical
  ext z
  simp only [zPureGenerators,Finset.mem_filter,Finset.mem_singleton]
  constructor
  · rintro ⟨hz,hr,hi⟩
    have hz' := (mem_minimalGenerators G z).mp hz
    rcases le_total z.2.2 C with hle | hle
    · exact hc.2 z hz'.1 (by simp [hr]) (by simp [hi]) hle
    · exact (hz'.2 _ hc.1 (Nat.zero_le _) (Nat.zero_le _) hle).symm
  · rintro rfl
    exact ⟨(mem_minimalGenerators G _).mpr hc,rfl,rfl⟩

theorem polynomialMinimal_seven_support_card (G : Finset Monomial)
    (hproper : (0,0,0) ∉ monomialClosure (G : Set Monomial)) :
    (minimalGenerators G).card = (xPureGenerators G).card+(yPureGenerators G).card+
      (zPureGenerators G).card+(xyGenerators G).card+(xzGenerators G).card+
      (yzGenerators G).card+(xyzGenerators G).card := by
  classical
  simp only [xPureGenerators,yPureGenerators,zPureGenerators,xyGenerators,xzGenerators,yzGenerators,
    xyzGenerators,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  have hn := minimal_support_exhaustive _ hproper g ((mem_minimalGenerators G g).mp hg)
  by_cases hr : g.1=0 <;> by_cases hi : g.2.1=0 <;> by_cases hj : g.2.2=0 <;>
    simp_all [Nat.pos_iff_ne_zero]

theorem polynomialMinimal_support_partition_card (G : Finset Monomial)
    (hproper : (0,0,0) ∉ monomialClosure (G : Set Monomial)) (A B C : ℕ)
    (ha : PolynomialMinimal (G : Set Monomial) (A,0,0))
    (hb : PolynomialMinimal (G : Set Monomial) (0,B,0))
    (hc : PolynomialMinimal (G : Set Monomial) (0,0,C)) :
    (minimalGenerators G).card = 3+(xyGenerators G).card+(xzGenerators G).card+
      (yzGenerators G).card+(xyzGenerators G).card := by
  rw [polynomialMinimal_seven_support_card G hproper,xPureGenerators_eq_singleton G A ha,
    yPureGenerators_eq_singleton G B hb,zPureGenerators_eq_singleton G C hc]
  simp

theorem positive_x_cutCost_eq_supportCount (G : Finset Monomial) (A : ℕ)
    (ha : PolynomialMinimal (G : Set Monomial) (A,0,0)) :
    ((allPositiveXCuts G A).map cutCost).sum =
      (xyGenerators G).card+(xzGenerators G).card+2*(xyzGenerators G).card := by
  classical
  rw [positive_x_cutCost_eq_minimal_sum G A ha]
  simp only [xyGenerators,xzGenerators,xyzGenerators,Finset.card_eq_sum_ones,
    Finset.sum_filter,two_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  by_cases hr : g.1=0 <;> by_cases hi : g.2.1=0 <;> by_cases hj : g.2.2=0 <;>
    simp [cutCost,hr,hi,hj,Nat.pos_iff_ne_zero]

theorem polynomialMinimal_card_eq (G : Finset Monomial) :
    Nat.card {z // PolynomialMinimal (G : Set Monomial) z}=(minimalGenerators G).card :=
  Nat.subtype_card _ (mem_minimalGenerators G)

theorem fullySupported_card_eq (G : Finset Monomial) :
    Nat.card {z // PolynomialMinimal (G : Set Monomial) z ∧ L5A2C4OR22.FullySupported z}=
      (xyzGenerators G).card := by
  classical
  apply Nat.subtype_card
  intro z
  simp only [xyzGenerators,Finset.mem_filter,mem_minimalGenerators,L5A2C4OR22.FullySupported]

/-- Universal finite slice ledger. No restriction on the number of fully supported minima is needed. -/
theorem abstract_monomial_socle_bound_general (G : Finset Monomial)
    (hproper : (0,0,0) ∉ monomialClosure (G : Set Monomial))
    (haxes : ∃ a b c : ℕ, 0<a ∧ 0<b ∧ 0<c ∧
      (a,0,0) ∈ monomialClosure (G : Set Monomial) ∧
      (0,b,0) ∈ monomialClosure (G : Set Monomial) ∧
      (0,0,c) ∈ monomialClosure (G : Set Monomial)) :
    Nat.card {z // MonomialSocle (G : Set Monomial) z}+2 ≤
      Nat.card {z // PolynomialMinimal (G : Set Monomial) z}+
      Nat.card {z // PolynomialMinimal (G : Set Monomial) z ∧ L5A2C4OR22.FullySupported z} := by
  obtain ⟨a,b,c,_,_,_,ha,hb,hc⟩ := haxes
  obtain ⟨A,⟨hA,ha⟩,_⟩ := pureX_minimum_exists_unique _ hproper a ha
  obtain ⟨B,⟨hB,hb⟩,_⟩ := pureY_minimum_exists_unique _ hproper b hb
  obtain ⟨C,⟨hC,hc⟩,_⟩ := pureZ_minimum_exists_unique _ hproper c hc
  have hdeath := socle_card_le_global_cutDeaths G A B C ha.1 hb.1 hc.1
  have hseq := sequentialCuts_death_bound (allPositiveXCuts G A)
    (sliceFinset (G : Set Monomial) 0 B C hb.1 hc.1)
    (sliceFinset_downwardClosed _ 0 B C hb.1 hc.1)
  have hinit := initialSlice_corner_bound G B C hB hC hb hc
  change (corners (sliceFinset (G : Set Monomial) 0 B C hb.1 hc.1)).card ≤ _ at hinit
  rw [positive_x_cutCost_eq_supportCount G A ha] at hseq
  have hsupport := polynomialMinimal_support_partition_card G hproper A B C ha hb hc
  rw [polynomialMinimal_card_eq,fullySupported_card_eq]
  omega

/-- Exact original T6 binder; greatest one-interior-generator assumption is retained, not strengthened. -/
theorem abstract_monomial_socle_bound (G : Finset Monomial)
    (hproper : (0,0,0) ∉ monomialClosure (G : Set Monomial))
    (haxes : ∃ a b c : ℕ, 0<a ∧ 0<b ∧ 0<c ∧
      (a,0,0) ∈ monomialClosure (G : Set Monomial) ∧
      (0,b,0) ∈ monomialClosure (G : Set Monomial) ∧
      (0,0,c) ∈ monomialClosure (G : Set Monomial))
    (_hiota : Nat.card {z // PolynomialMinimal (G : Set Monomial) z ∧
      L5A2C4OR22.FullySupported z} ≤ 1) :
    Nat.card {z // MonomialSocle (G : Set Monomial) z}+2 ≤
      Nat.card {z // PolynomialMinimal (G : Set Monomial) z}+
      Nat.card {z // PolynomialMinimal (G : Set Monomial) z ∧ L5A2C4OR22.FullySupported z} :=
  abstract_monomial_socle_bound_general G hproper haxes

open L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR19 L5A2C4OR22
variable {Gamma : NumericalSemigroup}

theorem actual_chart_minimal_finite (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : {z | ChartMinimal B e HD z}.Finite := by
  apply (Set.finite_Iic (H0 B e,c2 B e,c3 B e)).subset
  intro z hz
  exact chartMinimal_bounds B e HD hz

/-- Exactly the true chart minima: redundant PC and the central relation are not counted. -/
def actualJ0Generators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Finset Monomial :=
  (actual_chart_minimal_finite B e HD).toFinset

theorem mem_actualJ0Generators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) :
    z ∈ actualJ0Generators B e HD ↔ ChartMinimal B e HD z := Set.Finite.mem_toFinset _

theorem actualJ0_closure_eq (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) :
    monomialClosure (actualJ0Generators B e HD : Set Monomial)=
      monomialClosure (chartGenerators B e HD) := by
  ext z
  constructor
  · rintro ⟨g,hg,hr,hi,hj⟩
    exact monomialClosure_upward ((mem_actualJ0Generators B e HD g).mp hg).1 hr hi hj
  · intro hz
    obtain ⟨g,hg,hr,hi,hj⟩ := monomialClosure_minimal_divisor _ z hz
    exact ⟨g,(mem_actualJ0Generators B e HD g).mpr hg,hr,hi,hj⟩

theorem actualJ0_polynomialMinimal_iff (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) :
    PolynomialMinimal (actualJ0Generators B e HD : Set Monomial) z ↔ ChartMinimal B e HD z := by
  simp only [PolynomialMinimal,actualJ0_closure_eq,ChartMinimal]

theorem actualJ0_socle_iff (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) :
    MonomialSocle (actualJ0Generators B e HD : Set Monomial) z ↔
      MonomialSocle (chartGenerators B e HD) z := by
  simp only [MonomialSocle,actualJ0_closure_eq]

theorem actualJ0_proper {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    (0,0,0) ∉ monomialClosure (actualJ0Generators P.M.base R.e R.HD : Set Monomial) := by
  rw [actualJ0_closure_eq]
  intro hzero
  have heq := (actual_pureB_chart_minimal R hm hn).2 _ hzero le_rfl (Nat.zero_le _) le_rfl
  have hz := congrArg (fun z : Monomial => z.2.1) heq
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hs := coherent_coefficients P.M.base R.e R.HD
  simp only [Prod.fst,Prod.snd] at hz
  omega

theorem actualJ0_proper_artinian {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    (0,0,0) ∉ monomialClosure (actualJ0Generators P.M.base R.e R.HD : Set Monomial) ∧
    ∃ a b c : ℕ, 0<a ∧ 0<b ∧ 0<c ∧
      (a,0,0) ∈ monomialClosure (actualJ0Generators P.M.base R.e R.HD : Set Monomial) ∧
      (0,b,0) ∈ monomialClosure (actualJ0Generators P.M.base R.e R.HD : Set Monomial) ∧
      (0,0,c) ∈ monomialClosure (actualJ0Generators P.M.base R.e R.HD : Set Monomial) := by
  have hproper := actualJ0_proper R hm hn
  refine ⟨hproper,H0 P.M.base R.e,c2 P.M.base R.e,c3 P.M.base R.e,?_,?_,?_,?_,?_,?_⟩
  · by_contra h
    have hzero : H0 P.M.base R.e=0 := by omega
    apply hproper
    rw [actualJ0_closure_eq]
    exact ⟨_,Or.inl (Or.inl rfl),by simp [hzero],le_rfl,le_rfl⟩
  · have hp := coherent_coefficients_positive P.M.base R.e R.HD
    have hs := coherent_coefficients P.M.base R.e R.HD
    omega
  · have hp := coherent_coefficients_positive P.M.base R.e R.HD
    have hs := coherent_coefficients P.M.base R.e R.HD
    omega
  · rw [actualJ0_closure_eq]
    exact ⟨_,Or.inl (Or.inl rfl),le_rfl,le_rfl,le_rfl⟩
  · rw [actualJ0_closure_eq]
    exact (actual_pureB_chart_minimal R hm hn).1
  · rw [actualJ0_closure_eq]
    exact (actual_pureC_chart_minimal R hm hn).1

theorem actualJ0_iota_le_one {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    Nat.card {z // PolynomialMinimal (actualJ0Generators P.M.base R.e R.HD : Set Monomial) z ∧
      FullySupported z} ≤ 1 := by
  simp only [actualJ0_polynomialMinimal_iff]
  change fullySupportedGeneratorCount P.M.base R.e R.HD ≤ 1
  rw [actual_fullySupported_generator_count R hm hn]
  rcases principal_iota_zero_or_one P.M.base R.e R.HD with h | h <;> omega

theorem actual_T6_socle_bound {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    Nat.card {z // MonomialSocle (chartGenerators P.M.base R.e R.HD) z}+2 ≤
      chartGeneratorCount P.M.base R.e R.HD+fullySupportedGeneratorCount P.M.base R.e R.HD := by
  have hpa := actualJ0_proper_artinian R hm hn
  have h := abstract_monomial_socle_bound (actualJ0Generators P.M.base R.e R.HD)
    hpa.1 hpa.2 (actualJ0_iota_le_one R hm hn)
  simpa only [actualJ0_socle_iff,actualJ0_polynomialMinimal_iff,
    chartGeneratorCount,fullySupportedGeneratorCount,ChartMinimalVectors] using h

theorem actual_T5_T6_socle_source_bound {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    Nat.card {z // MonomialSocle (chartGenerators P.M.base R.e R.HD) z} ≤
      P.sourceCount+PB_epsilon P.M.base R.e R.HD+principal_iota P.M.base R.e R.HD := by
  have h := actual_T6_socle_bound R hm hn
  rw [actual_chart_generator_count R hm hn,actual_fullySupported_generator_count R hm hn] at h
  omega

end NS25Lean.L5A2C4OR24
