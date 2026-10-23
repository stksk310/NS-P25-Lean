import NS25Lean.P2BranchBPrefixFAntichain

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}
local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

local instance (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Finite (NonsymmetricPrefixFSources R hB hQ) :=
  nonsymmetric_prefix_F_sources_finite R hB hQ
local instance (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Fintype (NonsymmetricPrefixFSources R hB hQ) :=
  Fintype.ofFinite _
local instance (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) : LinearOrder (NonsymmetricPrefixFSources R hB hQ) :=
  LinearOrder.lift' (fun s => (nonsymmetricFSourceCoordinate R hB hQ s).1)
    (nonsymmetric_F_source_x_injective R hB hQ)

abbrev nonsymmetricFOrderSize (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  Fintype.card (NonsymmetricPrefixFSources R hB hQ)

def nonsymmetricFOrderedSource (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Fin (nonsymmetricFOrderSize R hB hQ) ↪o NonsymmetricPrefixFSources R hB hQ :=
  Finset.univ.orderEmbOfFin (by simp)

def nonsymmetricFOrderedCoordinate (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (k : Fin (nonsymmetricFOrderSize R hB hQ)) : ℕ×ℕ :=
  nonsymmetricFSourceCoordinate R hB hQ (nonsymmetricFOrderedSource R hB hQ k)

theorem nonsymmetric_F_order_card (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricFOrderSize R hB hQ=Nat.card (NonsymmetricPrefixFSources R hB hQ) :=
  Nat.card_eq_fintype_card.symm

theorem nonsymmetric_F_order_surjective (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Surjective (nonsymmetricFOrderedSource R hB hQ) := by
  intro s
  let e : Fin (nonsymmetricFOrderSize R hB hQ) ≃o
      (Finset.univ : Finset (NonsymmetricPrefixFSources R hB hQ)) :=
    Finset.univ.orderIsoOfFin (by simp)
  refine ⟨e.symm ⟨s,Finset.mem_univ s⟩,?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨s,Finset.mem_univ s⟩)

theorem nonsymmetric_F_order_x_strict (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    StrictMono (fun k => (nonsymmetricFOrderedCoordinate R hB hQ k).1) := by
  intro i j h
  exact (nonsymmetricFOrderedSource R hB hQ).strictMono h

theorem nonsymmetric_F_order_y_strict (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    StrictAnti (fun k => (nonsymmetricFOrderedCoordinate R hB hQ k).2) := by
  intro i j h
  exact nonsymmetric_F_source_y_strict_antitone R hB hQ _ _
    (nonsymmetric_F_order_x_strict R hB hQ h)

theorem nonsymmetric_F_order_spec (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (k : Fin (nonsymmetricFOrderSize R hB hQ)) :
    NonsymmetricLDomain R (nonsymmetricFOrderedCoordinate R hB hQ k).1
      (nonsymmetricFOrderedCoordinate R hB hQ k).2 ∧
    0 < (nonsymmetricFOrderedCoordinate R hB hQ k).1 ∧
    0 < (nonsymmetricFOrderedCoordinate R hB hQ k).2 := by
  have h := nonsymmetric_F_source_coordinate_spec R hB hQ (nonsymmetricFOrderedSource R hB hQ k)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

def nonsymmetricAdjacentLeft (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (k : Fin (nonsymmetricFOrderSize R hB hQ-1)) : Fin (nonsymmetricFOrderSize R hB hQ) :=
  ⟨k.val,by omega⟩
def nonsymmetricAdjacentRight (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (k : Fin (nonsymmetricFOrderSize R hB hQ-1)) : Fin (nonsymmetricFOrderSize R hB hQ) :=
  ⟨k.val+1,by omega⟩

def NonsymmetricAdjacentBad (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (k : Fin (nonsymmetricFOrderSize R hB hQ-1)) : Prop :=
  nsP R ≤ (nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentRight R hB hQ k)).1 ∧
  nsQ R ≤ (nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentLeft R hB hQ k)).2

theorem nonsymmetric_adjacent_bad_at_most_one (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (i j : Fin (nonsymmetricFOrderSize R hB hQ-1))
    (hi : NonsymmetricAdjacentBad R hB hQ i) (hj : NonsymmetricAdjacentBad R hB hQ j) : i=j := by
  have no_lt {i j : Fin (nonsymmetricFOrderSize R hB hQ-1)}
      (hi : NonsymmetricAdjacentBad R hB hQ i) (hj : NonsymmetricAdjacentBad R hB hQ j)
      (hij : i<j) : False := by
    have hle : nonsymmetricAdjacentRight R hB hQ i ≤ nonsymmetricAdjacentLeft R hB hQ j := by
      change i.val+1 ≤ j.val
      exact hij
    have hx := (nonsymmetric_F_order_x_strict R hB hQ).monotone hle
    have hd := (nonsymmetric_F_order_spec R hB hQ (nonsymmetricAdjacentLeft R hB hQ j)).1.2.2
    have h1 := hi.1; have h2 := hj.2
    rcases hd with h | h <;> omega
  rcases lt_trichotomy i j with h | h | h
  · exact (no_lt hi hj h).elim
  · exact h
  · exact (no_lt hj hi h).elim

private theorem source_zero_quadrant (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (s : NonsymmetricPrefixFSources R hB hQ) {x y : ℕ}
    (hx : (nonsymmetricFSourceCoordinate R hB hQ s).1 ≤ x)
    (hy : (nonsymmetricFSourceCoordinate R hB hQ s).2 ≤ y) :
    nonsymmetricPrefixDiagramHeight R hB hQ x y=0 := by
  obtain ⟨ell,he⟩ := nonsymmetric_F_source_coordinate_return R hB hQ s
  apply (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ x y).mpr
  exact ⟨ell,by simpa only [← he] using hx,by simpa only [← he] using hy⟩

theorem nonsymmetric_adjacent_F_ordinary_notch (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (k : Fin (nonsymmetricFOrderSize R hB hQ-1))
    (hgood : ¬ NonsymmetricAdjacentBad R hB hQ k) :
    NonsymmetricOrdinaryNotch R hB hQ
      ((nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentRight R hB hQ k)).1-1)
      ((nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentLeft R hB hQ k)).2-1) := by
  let l := nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentLeft R hB hQ k)
  let r := nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentRight R hB hQ k)
  change ¬ (nsP R ≤ r.1 ∧ nsQ R ≤ l.2) at hgood
  have hl := nonsymmetric_F_order_spec R hB hQ (nonsymmetricAdjacentLeft R hB hQ k)
  have hr := nonsymmetric_F_order_spec R hB hQ (nonsymmetricAdjacentRight R hB hQ k)
  change NonsymmetricLDomain R l.1 l.2 ∧ 0 < l.1 ∧ 0 < l.2 at hl
  change NonsymmetricLDomain R r.1 r.2 ∧ 0 < r.1 ∧ 0 < r.2 at hr
  have hstep : nonsymmetricAdjacentLeft R hB hQ k < nonsymmetricAdjacentRight R hB hQ k := by
    change k.val < k.val+1; omega
  have hx : l.1 < r.1 := nonsymmetric_F_order_x_strict R hB hQ hstep
  have hy : r.2 < l.2 := nonsymmetric_F_order_y_strict R hB hQ hstep
  have hdom : NonsymmetricLDomain R r.1 l.2 := by
    refine ⟨hr.1.1,hl.1.2.1,?_⟩
    by_cases hi : r.1 < nsP R
    · exact Or.inl hi
    · right
      by_contra hj
      apply hgood
      exact ⟨by omega,by omega⟩
  have hnz : nonsymmetricPrefixDiagramHeight R hB hQ (r.1-1) (l.2-1) ≠ 0 := by
    intro hz
    obtain ⟨ell,heX,heY⟩ := (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mp hz
    obtain ⟨s,hsX,hsY⟩ := nonsymmetric_return_has_minimal_F_predecessor R hB hQ ell
    obtain ⟨j,hj⟩ := nonsymmetric_F_order_surjective R hB hQ s
    rw [← hj] at hsX hsY
    have hX : (nonsymmetricFOrderedCoordinate R hB hQ j).1 ≤ r.1-1 := le_trans hsX heX
    have hY : (nonsymmetricFOrderedCoordinate R hB hQ j).2 ≤ l.2-1 := le_trans hsY heY
    have hJR : j < nonsymmetricAdjacentRight R hB hQ k := by
      by_contra h
      have hle : nonsymmetricAdjacentRight R hB hQ k ≤ j := le_of_not_gt h
      have hm := (nonsymmetric_F_order_x_strict R hB hQ).monotone hle
      change r.1 ≤ (nonsymmetricFOrderedCoordinate R hB hQ j).1 at hm
      omega
    have hLJ : nonsymmetricAdjacentLeft R hB hQ k < j := by
      by_contra h
      have hle : j ≤ nonsymmetricAdjacentLeft R hB hQ k := le_of_not_gt h
      have hm := (nonsymmetric_F_order_y_strict R hB hQ).antitone hle
      change l.2 ≤ (nonsymmetricFOrderedCoordinate R hB hQ j).2 at hm
      omega
    change j.val < k.val+1 at hJR
    change k.val < j.val at hLJ
    omega
  have hSE : nonsymmetricPrefixDiagramHeight R hB hQ r.1 (l.2-1)=0 := by
    apply source_zero_quadrant R hB hQ (nonsymmetricFOrderedSource R hB hQ (nonsymmetricAdjacentRight R hB hQ k))
    · exact le_refl _
    · change r.2 ≤ l.2-1; omega
  have hNW : nonsymmetricPrefixDiagramHeight R hB hQ (r.1-1) l.2=0 := by
    apply source_zero_quadrant R hB hQ (nonsymmetricFOrderedSource R hB hQ (nonsymmetricAdjacentLeft R hB hQ k))
    · change l.1 ≤ r.1-1; omega
    · exact le_refl _
  have hNE : nonsymmetricPrefixDiagramHeight R hB hQ r.1 l.2=0 := by
    apply source_zero_quadrant R hB hQ (nonsymmetricFOrderedSource R hB hQ (nonsymmetricAdjacentLeft R hB hQ k))
    · change l.1 ≤ r.1; omega
    · exact le_refl _
  change NonsymmetricOrdinaryNotch R hB hQ (r.1-1) (l.2-1)
  unfold NonsymmetricOrdinaryNotch
  simp only [Nat.sub_add_cancel (by omega : 1 ≤ r.1),Nat.sub_add_cancel (by omega : 1 ≤ l.2)]
  exact ⟨hdom,by omega,hSE,hNW,hNE⟩

def NonsymmetricGoodAdjacentIndices (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  {k : Fin (nonsymmetricFOrderSize R hB hQ-1) // ¬ NonsymmetricAdjacentBad R hB hQ k}
def NonsymmetricBadAdjacentIndices (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  {k : Fin (nonsymmetricFOrderSize R hB hQ-1) // NonsymmetricAdjacentBad R hB hQ k}

def nonsymmetricAdjacentNotch (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (k : NonsymmetricGoodAdjacentIndices R hB hQ) : NonsymmetricOrdinaryNotches R hB hQ :=
  ⟨((nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentRight R hB hQ k.val)).1-1,
    (nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentLeft R hB hQ k.val)).2-1),
    nonsymmetric_adjacent_F_ordinary_notch R hB hQ k.val k.property⟩

theorem nonsymmetricAdjacentNotch_injective (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricAdjacentNotch R hB hQ) := by
  intro i j he
  have hv := congrArg (fun p : NonsymmetricOrdinaryNotches R hB hQ => p.val.1) he
  change (nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentRight R hB hQ i.val)).1-1=
    (nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentRight R hB hQ j.val)).1-1 at hv
  have hi := (nonsymmetric_F_order_spec R hB hQ (nonsymmetricAdjacentRight R hB hQ i.val)).2.1
  have hj := (nonsymmetric_F_order_spec R hB hQ (nonsymmetricAdjacentRight R hB hQ j.val)).2.1
  have hx : (nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentRight R hB hQ i.val)).1=
      (nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentRight R hB hQ j.val)).1 := by omega
  have hk := (nonsymmetric_F_order_x_strict R hB hQ).injective hx
  have hval := congrArg Fin.val hk
  change i.val.val+1=j.val.val+1 at hval
  apply Subtype.ext
  apply Fin.ext
  omega

theorem nonsymmetric_F_order_positive (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    0 < nonsymmetricFOrderSize R hB hQ := by
  obtain ⟨ell⟩ := nonsymmetricReturnNonempty R hQ
  obtain ⟨s,_⟩ := nonsymmetric_return_has_minimal_F_predecessor R hB hQ ell
  exact Fintype.card_pos_iff.mpr ⟨s⟩

theorem nonsymmetric_adjacent_partition_card (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Nat.card (NonsymmetricGoodAdjacentIndices R hB hQ)+
      Nat.card (NonsymmetricBadAdjacentIndices R hB hQ)=nonsymmetricFOrderSize R hB hQ-1 := by
  have h := Nat.card_congr (Equiv.sumCompl (NonsymmetricAdjacentBad R hB hQ))
  have h' : Nat.card (NonsymmetricBadAdjacentIndices R hB hQ)+
      Nat.card (NonsymmetricGoodAdjacentIndices R hB hQ)=nonsymmetricFOrderSize R hB hQ-1 := by
    simpa only [Nat.card_sum,Nat.card_fin, NonsymmetricBadAdjacentIndices,
      NonsymmetricGoodAdjacentIndices] using h
  omega

theorem nonsymmetric_adjacent_bad_card_le_one (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Nat.card (NonsymmetricBadAdjacentIndices R hB hQ) ≤ 1 := by
  have hi : Function.Injective (fun _ : NonsymmetricBadAdjacentIndices R hB hQ => ()) := by
    intro i j _
    exact Subtype.ext (nonsymmetric_adjacent_bad_at_most_one R hB hQ i.val j.val i.property j.property)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_unit] using Nat.card_le_card_of_injective _ hi

theorem nonsymmetric_CENTER_no_bad_adjacency (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hcenter : ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) :
    ∀ k, ¬ NonsymmetricAdjacentBad R hB hQ k := by
  obtain ⟨s,hX,hY⟩ := (nonsymmetric_prefix_CENTER_iff_minimal_F_CENTER R hB hQ).mp hcenter
  obtain ⟨j,hj⟩ := nonsymmetric_F_order_surjective R hB hQ s
  rw [← hj] at hX hY
  change (nonsymmetricFOrderedCoordinate R hB hQ j).1 < nsP R at hX
  change (nonsymmetricFOrderedCoordinate R hB hQ j).2 < nsQ R at hY
  intro k hk
  by_cases hle : j ≤ nonsymmetricAdjacentLeft R hB hQ k
  · have hy := (nonsymmetric_F_order_y_strict R hB hQ).antitone hle
    have hbad := hk.2
    omega
  · have hle' : nonsymmetricAdjacentRight R hB hQ k ≤ j := by
      change k.val+1 ≤ j.val
      change ¬ j.val ≤ k.val at hle
      omega
    have hx := (nonsymmetric_F_order_x_strict R hB hQ).monotone hle'
    have hbad := hk.1
    omega

theorem nonsymmetric_prefix_delta_epsilon_le_one (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Nat.card (NonsymmetricPrefixCenterSlot R hB)+
      Nat.card (NonsymmetricBadAdjacentIndices R hB hQ) ≤ 1 := by
  by_cases hc : ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R
  · letI : IsEmpty (NonsymmetricBadAdjacentIndices R hB hQ) :=
      ⟨fun k => nonsymmetric_CENTER_no_bad_adjacency R hB hQ hc k.val k.property⟩
    rw [Nat.card_of_isEmpty (α := NonsymmetricBadAdjacentIndices R hB hQ),
      nonsymmetric_prefix_center_slot_count R hB,if_pos hc]
  · rw [nonsymmetric_prefix_center_slot_count R hB,if_neg hc,zero_add]
    exact nonsymmetric_adjacent_bad_card_le_one R hB hQ

theorem nonsymmetric_adjacent_good_count_le_notches (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Nat.card (NonsymmetricGoodAdjacentIndices R hB hQ) ≤
      Nat.card (NonsymmetricOrdinaryNotches R hB hQ) := by
  letI : Finite (L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ)) := Subtype.finite
  letI : Finite (NonsymmetricOrdinaryNotches R hB hQ) :=
    Finite.of_injective _ (nonsymmetricOrdinaryNotchResource_injective R hB hQ)
  exact Nat.card_le_card_of_injective _ (nonsymmetricAdjacentNotch_injective R hB hQ)

theorem nonsymmetric_prefix_notch_coverage_bound (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (_hbal : NonsymmetricBalancedReturns R hB) :
    Nat.card (NonsymmetricPrefixFSources R hB hQ)+
      Nat.card (NonsymmetricPrefixCenterSlot R hB) ≤
      Nat.card (NonsymmetricOrdinaryNotches R hB hQ)+2 := by
  have hp := nonsymmetric_F_order_positive R hB hQ
  have hpart := nonsymmetric_adjacent_partition_card R hB hQ
  have hc := nonsymmetric_prefix_delta_epsilon_le_one R hB hQ
  have hn := nonsymmetric_adjacent_good_count_le_notches R hB hQ
  rw [nonsymmetric_F_order_card R hB hQ] at hp hpart
  omega

theorem nonsymmetric_no_CENTER_balanced_bad_exists (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB)
    (hc : ¬ ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) :
    Nonempty (NonsymmetricBadAdjacentIndices R hB hQ) := by
  have hn : ∀ s : NonsymmetricPrefixFSources R hB hQ,
      ¬ ((nonsymmetricFSourceCoordinate R hB hQ s).1 < nsP R ∧
        (nonsymmetricFSourceCoordinate R hB hQ s).2 < nsQ R) := by
    intro s hs
    exact hc ((nonsymmetric_prefix_CENTER_iff_minimal_F_CENTER R hB hQ).mpr ⟨s,hs⟩)
  obtain ⟨el,hel⟩ := hbal.1
  obtain ⟨sl,hslx,hsly⟩ := nonsymmetric_return_has_minimal_F_predecessor R hB hQ el
  obtain ⟨il,hil⟩ := nonsymmetric_F_order_surjective R hB hQ sl
  have hleft : (nonsymmetricFOrderedCoordinate R hB hQ il).1 < nsP R := by
    change (nonsymmetricFSourceCoordinate R hB hQ _).1 < _
    rw [hil]
    omega
  obtain ⟨er,her⟩ := hbal.2
  obtain ⟨sr,hsrx,hsry⟩ := nonsymmetric_return_has_minimal_F_predecessor R hB hQ er
  have hright : nsP R ≤ (nonsymmetricFSourceCoordinate R hB hQ sr).1 := by
    have hh := hn sr
    omega
  obtain ⟨ir,hir⟩ := nonsymmetric_F_order_surjective R hB hQ sr
  have hex : ∃ k : ℕ, ∃ hk : k < nonsymmetricFOrderSize R hB hQ,
      nsP R ≤ (nonsymmetricFOrderedCoordinate R hB hQ ⟨k,hk⟩).1 := by
    exact ⟨ir.val,ir.isLt,by change nsP R ≤ (nonsymmetricFSourceCoordinate R hB hQ _).1; rw [hir]; exact hright⟩
  let k := Nat.find hex
  obtain ⟨hk,hkx⟩ := Nat.find_spec hex
  change nsP R ≤ (nonsymmetricFOrderedCoordinate R hB hQ ⟨k,hk⟩).1 at hkx
  have hkpos : 0 < k := by
    by_contra h
    have hzero : k=0 := by omega
    have hle : (⟨k,hk⟩ : Fin (nonsymmetricFOrderSize R hB hQ)) ≤ il := by
      change k ≤ il.val
      omega
    have hm := (nonsymmetric_F_order_x_strict R hB hQ).monotone hle
    omega
  have hp : k-1 < nonsymmetricFOrderSize R hB hQ := by omega
  have hpx : (nonsymmetricFOrderedCoordinate R hB hQ ⟨k-1,hp⟩).1 < nsP R := by
    have hmin := Nat.find_min hex (by omega : k-1 < k)
    by_contra h
    exact hmin ⟨hp,by omega⟩
  have hpy : nsQ R ≤ (nonsymmetricFOrderedCoordinate R hB hQ ⟨k-1,hp⟩).2 := by
    have hh := hn (nonsymmetricFOrderedSource R hB hQ ⟨k-1,hp⟩)
    change ¬ ((nonsymmetricFOrderedCoordinate R hB hQ ⟨k-1,hp⟩).1 < nsP R ∧
      (nonsymmetricFOrderedCoordinate R hB hQ ⟨k-1,hp⟩).2 < nsQ R) at hh
    omega
  let a : Fin (nonsymmetricFOrderSize R hB hQ-1) := ⟨k-1,by omega⟩
  have he : nonsymmetricAdjacentRight R hB hQ a = ⟨k,hk⟩ := by
    apply Fin.ext
    change k-1+1=k
    omega
  refine ⟨⟨a,?_⟩⟩
  constructor
  · rw [he]
    exact hkx
  · exact hpy

theorem nonsymmetric_prefix_delta_epsilon (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    Nat.card (NonsymmetricPrefixCenterSlot R hB)+
      Nat.card (NonsymmetricBadAdjacentIndices R hB hQ)=1 := by
  have hle := nonsymmetric_prefix_delta_epsilon_le_one R hB hQ
  by_cases hc : ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R
  · rw [nonsymmetric_prefix_center_slot_count R hB,if_pos hc] at hle ⊢
    omega
  · letI : Nonempty (NonsymmetricBadAdjacentIndices R hB hQ) :=
      nonsymmetric_no_CENTER_balanced_bad_exists R hB hQ hbal hc
    letI : Finite (NonsymmetricBadAdjacentIndices R hB hQ) := Subtype.finite
    have hp : 0 < Nat.card (NonsymmetricBadAdjacentIndices R hB hQ) := Nat.card_pos
    rw [nonsymmetric_prefix_center_slot_count R hB,if_neg hc] at hle ⊢
    omega

end NS25Lean.L5A2BFinalRepair
