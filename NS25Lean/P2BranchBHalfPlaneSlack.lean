import NS25Lean.P2BranchBPrefixSourceLoss

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
set_option maxHeartbeats 800000
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}
local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

theorem nonsymmetric_no_left_return_geometry (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M)
    (hno : ¬∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).1 < nsP R) :
    ∀ ell, nsP R ≤ (nonsymmetricReturnTuple R hB ell).1 ∧
      (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := by
  intro ell
  have hn : ¬ (nonsymmetricReturnTuple R hB ell).1 < nsP R := fun h => hno ⟨ell,h⟩
  have dom := (nonsymmetricReturnTuple_spec R hB ell).1
  rcases dom.2.2 with hi | hj
  · exact (hn hi).elim
  · exact ⟨by omega,hj⟩

theorem nonsymmetric_no_left_prefix_corner_profile (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hno : ¬∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).1 < nsP R) :
    let D := nonsymmetricPrefixRouting R hQ
    0 < nonsymmetricDR R hB ∧
    D.u (nonsymmetricKappa1 R)=nonsymmetricDR R hB ∧
    D.v (nonsymmetricKappa1 R)=nonsymmetricDR R hB ∧
    D.u (D.c (nonsymmetricKappa1 R))=0 ∧
    D.v (D.b (nonsymmetricKappa1 R))=0 ∧
    nonsymmetricPrefixDiagramHeight R hB hQ (nsC2 R-1) (nsQ R-1)=0 := by
  have geom := nonsymmetric_no_left_return_geometry R hB hno
  obtain ⟨ell0⟩ := nonsymmetricReturnNonempty R hQ
  have hright : ∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R :=
    ⟨ell0,(geom ell0).2⟩
  have hp := nonsymmetric_coefficients R
  have hpos : 0 < nonsymmetricDR R hB := lt_of_lt_of_le
    (nonsymmetricReturnTuple_spec R hB ell0).2.2.2.1
    (nonsymmetric_depth_le_max R hB (p:=fun ell => (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) ell0 (geom ell0).2)
  have hmax : nonsymmetricDR R hB < nsU R := nonsymmetric_depth_max_lt R hB hp.2.2.1
    (fun ell => (nonsymmetricReturnTuple_spec R hB ell).2.2.2.2.2.1)
  have height0 : nonsymmetricPrefixDiagramHeight R hB hQ (nsC2 R-1) (nsQ R-1)=0 := by
    apply (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mpr
    have S := nonsymmetricReturnTuple_spec R hB ell0
    exact ⟨ell0,by have := S.1.1; omega,by have := (geom ell0).2; omega⟩
  have top : nonsymmetricPrefixDiagramHeight R hB hQ 0 (nsC3 R-1)=nsU R-nonsymmetricDR R hB := by
    apply le_antisymm
    · obtain ⟨ell,hj,he⟩ := nonsymmetric_depth_max_attained R hB hright
      apply nonsymmetric_prefix_diagram_le_candidate R hB hQ
      refine ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hj,?_,?_⟩))))⟩
      · have S := nonsymmetricReturnTuple_spec R hB ell
        have dc := S.1.2.1
        omega
      · rw [he]
    · obtain ⟨ell,hc⟩ := nonsymmetric_prefix_diagram_height_attained R hB hQ 0 (nsC3 R-1)
      have S := nonsymmetricReturnTuple_spec R hB ell
      have gg := geom ell
      have dm := nonsymmetric_depth_le_max R hB (p:=fun ell => (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) ell gg.2
      change _ ≤ nonsymmetricDR R hB at dm
      rcases hc with h | h | h | h | h | h <;> omega
  have bottom {x : ℕ} (hx : nsZ R-1 ≤ x) :
      nonsymmetricPrefixDiagramHeight R hB hQ x 0=nsC1 R-nonsymmetricDR R hB := by
    apply le_antisymm
    · obtain ⟨ell,hj,he⟩ := nonsymmetric_depth_max_attained R hB hright
      have S := nonsymmetricReturnTuple_spec R hB ell
      have gg := geom ell
      apply nonsymmetric_prefix_diagram_le_candidate R hB hQ
      refine ⟨ell,Or.inr (Or.inr (Or.inl ⟨gg.1,?_,?_⟩))⟩
      · have hh := S.1.1
        omega
      · rw [he]
    · obtain ⟨ell,hc⟩ := nonsymmetric_prefix_diagram_height_attained R hB hQ x 0
      have S := nonsymmetricReturnTuple_spec R hB ell
      have gg := geom ell
      have dm := nonsymmetric_depth_le_max R hB (p:=fun ell => (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) ell gg.2
      change _ ≤ nonsymmetricDR R hB at dm
      rcases hc with h | h | h | h | h | h <;> omega
  have hd : NonsymmetricLDomain R (nsC2 R-1) (nsQ R-1) := by unfold NonsymmetricLDomain; omega
  have ht : NonsymmetricLDomain R 0 (nsC3 R-1) := by unfold NonsymmetricLDomain; omega
  have hb : NonsymmetricLDomain R (nsZ R-1) 0 := by unfold NonsymmetricLDomain; omega
  have hb' : NonsymmetricLDomain R (nsZ R) 0 := by unfold NonsymmetricLDomain; omega
  have rel := nonsymmetric_normalized_relations R
  have pred (n g : ℕ) (hn : 0 < n) : (n-1)*g+g=n*g := by
    have hs : n-1+1=n := by omega
    have h := congrArg (fun n => n*g) hs
    simpa only [add_mul,one_mul] using h
  have B := nonsymmetric_prefix_b_edge R hB hQ hd ht (carry:=nsU R) (by
    have h1 := pred (nsC2 R) (nsB R) (by omega)
    have h2 := pred (nsC3 R) (nsC R) (by omega)
    have hq := pred (nsQ R) (nsC R) (by omega)
    have r := rel.2.1
    have sum := congrArg (fun n => n*nsC R) hp.2.2.2.2.2.2.2.2
    simp only [add_mul] at sum
    simp only [zero_mul,zero_add]
    omega)
  have C := nonsymmetric_prefix_c_edge R hB hQ hd hb (carry:=nsC1 R) (by
    have h1 := pred (nsC2 R) (nsB R) (by omega)
    have hq := pred (nsQ R) (nsC R) (by omega)
    have hz := pred (nsZ R) (nsB R) (by omega)
    have sum := congrArg (fun n => n*nsB R) hp.2.2.2.2.2.2.2.1
    simp only [add_mul] at sum
    simp only [zero_mul,add_zero]
    have r := rel.1
    omega)
  have CB := nonsymmetric_prefix_b_edge R hB hQ hb hb' (carry:=0) (by
    have hz := pred (nsZ R) (nsB R) (by omega)
    simpa only [zero_mul,add_zero,zero_add] using hz)
  have BC := nonsymmetric_prefix_c_edge R hB hQ ht hb' (carry:=nsW R) (by
    have hz := pred (nsC3 R) (nsC R) (by omega)
    simpa only [zero_mul,zero_add,add_zero] using hz.trans rel.2.2)
  rw [height0,top] at B
  rw [height0,bottom (le_refl _)] at C
  rw [bottom (le_refl _),bottom (by omega)] at CB
  rw [top,bottom (by omega)] at BC
  have B2 := B.2; have C2 := C.2; have CB2 := CB.2; have BC2 := BC.2
  dsimp only
  refine ⟨hpos,?_,?_,?_,?_,height0⟩
  · change (nonsymmetricPrefixRouting R hQ).u (gridResidue P.M.base (nsReindex R) (nsC2 R-1) (nsQ R-1))=nonsymmetricDR R hB
    omega
  · change (nonsymmetricPrefixRouting R hQ).v (gridResidue P.M.base (nsReindex R) (nsC2 R-1) (nsQ R-1))=nonsymmetricDR R hB
    omega
  · rw [C.1]; omega
  · rw [B.1]; omega

theorem nonsymmetric_no_left_prefix_corner_resources (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hno : ¬∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).1 < nsP R) :
    L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (nonsymmetricPrefixRouting R hQ) (nonsymmetricKappa1 R) ∧
    Nonempty (FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R) (routingHB _ _) (routingHC _ _)) := by
  have profile := nonsymmetric_no_left_prefix_corner_profile R hB hQ hno
  have hp := nonsymmetric_coefficients R
  dsimp only at profile
  constructor
  · unfold L5A2C4I.ResidueData.ExactUnusedMergeReverseBase
    rw [profile.2.1,profile.2.2.1,profile.2.2.2.1,profile.2.2.2.2.1]
    omega
  · refine ⟨⟨nonsymmetricKappa1 R,?_,?_⟩⟩
    · change (nonsymmetricPrefixRouting R hQ).u (nonsymmetricKappa1 R) ≠ 0 ∧
        (nonsymmetricPrefixRouting R hQ).v (nonsymmetricKappa1 R) ≠ 0
      rw [profile.2.1,profile.2.2.1]
      omega
    · change nonsymmetricPrefixLambda R hQ _-nsA R ∉ (nsH R).asRelativeIdeal
      have hd : NonsymmetricLDomain R (nsC2 R-1) (nsQ R-1) := by unfold NonsymmetricLDomain; omega
      rw [nonsymmetric_prefix_height_formula R hB hQ hd,profile.2.2.2.2.2,Nat.cast_zero,zero_mul,zero_add]
      simpa only [Nat.cast_add,Nat.cast_mul] using nonsymmetric_canonical_a_predecessor_not_mem R hd

theorem nonsymmetric_no_right_return_geometry (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M)
    (hno : ¬∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) :
    ∀ ell, (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
      nsQ R ≤ (nonsymmetricReturnTuple R hB ell).2.1 := by
  intro ell
  have hn : ¬ (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := fun h => hno ⟨ell,h⟩
  have dom := (nonsymmetricReturnTuple_spec R hB ell).1
  rcases dom.2.2 with hi | hj
  · exact ⟨hi,by omega⟩
  · exact (hn hj).elim

theorem nonsymmetric_no_right_prefix_corner_profile (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hno : ¬∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) :
    let D := nonsymmetricPrefixRouting R hQ
    0 < nonsymmetricDL R hB ∧
    D.u (nonsymmetricKappa2 R)=nonsymmetricDL R hB ∧
    D.v (nonsymmetricKappa2 R)=nonsymmetricDL R hB ∧
    D.u (D.c (nonsymmetricKappa2 R))=0 ∧
    D.v (D.b (nonsymmetricKappa2 R))=0 ∧
    nonsymmetricPrefixDiagramHeight R hB hQ (nsP R-1) (nsC3 R-1)=0 := by
  have geom := nonsymmetric_no_right_return_geometry R hB hno
  obtain ⟨ell0⟩ := nonsymmetricReturnNonempty R hQ
  have hleft : ∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).1 < nsP R :=
    ⟨ell0,(geom ell0).1⟩
  have hp := nonsymmetric_coefficients R
  have hpos : 0 < nonsymmetricDL R hB := lt_of_lt_of_le
    (nonsymmetricReturnTuple_spec R hB ell0).2.2.2.1
    (nonsymmetric_depth_le_max R hB (p:=fun ell => (nonsymmetricReturnTuple R hB ell).1 < nsP R) ell0 (geom ell0).1)
  have hmax : nonsymmetricDL R hB < nsW R := nonsymmetric_depth_max_lt R hB hp.2.2.2.2.1
    (fun ell => (nonsymmetricReturnTuple_spec R hB ell).2.2.2.2.1)
  have height0 : nonsymmetricPrefixDiagramHeight R hB hQ (nsP R-1) (nsC3 R-1)=0 := by
    apply (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mpr
    have S := nonsymmetricReturnTuple_spec R hB ell0
    exact ⟨ell0,by have := (geom ell0).1; omega,by have := S.1.2.1; omega⟩
  have bottom : nonsymmetricPrefixDiagramHeight R hB hQ (nsC2 R-1) 0=nsW R-nonsymmetricDL R hB := by
    apply le_antisymm
    · obtain ⟨ell,hi,he⟩ := nonsymmetric_depth_max_attained R hB hleft
      apply nonsymmetric_prefix_diagram_le_candidate R hB hQ
      refine ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,?_,?_⟩))))⟩
      · have S := nonsymmetricReturnTuple_spec R hB ell
        have dc := S.1.1
        omega
      · rw [he]
    · obtain ⟨ell,hc⟩ := nonsymmetric_prefix_diagram_height_attained R hB hQ (nsC2 R-1) 0
      have S := nonsymmetricReturnTuple_spec R hB ell
      have gg := geom ell
      have dm := nonsymmetric_depth_le_max R hB (p:=fun ell => (nonsymmetricReturnTuple R hB ell).1 < nsP R) ell gg.1
      change _ ≤ nonsymmetricDL R hB at dm
      rcases hc with h | h | h | h | h | h <;> omega
  have side {y : ℕ} (hy : nsV R-1 ≤ y) :
      nonsymmetricPrefixDiagramHeight R hB hQ 0 y=nsC1 R-nonsymmetricDL R hB := by
    apply le_antisymm
    · obtain ⟨ell,hi,he⟩ := nonsymmetric_depth_max_attained R hB hleft
      have S := nonsymmetricReturnTuple_spec R hB ell
      have gg := geom ell
      apply nonsymmetric_prefix_diagram_le_candidate R hB hQ
      refine ⟨ell,Or.inr (Or.inr (Or.inr (Or.inl ⟨gg.2,?_,?_⟩)))⟩
      · have hh := S.1.2.1
        omega
      · rw [he]
    · obtain ⟨ell,hc⟩ := nonsymmetric_prefix_diagram_height_attained R hB hQ 0 y
      have S := nonsymmetricReturnTuple_spec R hB ell
      have gg := geom ell
      have dm := nonsymmetric_depth_le_max R hB (p:=fun ell => (nonsymmetricReturnTuple R hB ell).1 < nsP R) ell gg.1
      change _ ≤ nonsymmetricDL R hB at dm
      rcases hc with h | h | h | h | h | h <;> omega
  have hd : NonsymmetricLDomain R (nsP R-1) (nsC3 R-1) := by unfold NonsymmetricLDomain; omega
  have ht : NonsymmetricLDomain R (nsC2 R-1) 0 := by unfold NonsymmetricLDomain; omega
  have hs : NonsymmetricLDomain R 0 (nsV R-1) := by unfold NonsymmetricLDomain; omega
  have hs' : NonsymmetricLDomain R 0 (nsV R) := by unfold NonsymmetricLDomain; omega
  have rel := nonsymmetric_normalized_relations R
  have pred (n g : ℕ) (hn : 0 < n) : (n-1)*g+g=n*g := by
    have h := congrArg (fun n => n*g) (show n-1+1=n by omega)
    simpa only [add_mul,one_mul] using h
  have C := nonsymmetric_prefix_c_edge R hB hQ hd ht (carry:=nsW R) (by
    have h1 := pred (nsC3 R) (nsC R) (by omega)
    have h2 := pred (nsC2 R) (nsB R) (by omega)
    have hq := pred (nsP R) (nsB R) (by omega)
    have r := rel.2.2
    have sum := congrArg (fun n => n*nsB R) hp.2.2.2.2.2.2.2.1
    simp only [add_mul] at sum
    simp only [zero_mul,add_zero]
    omega)
  have B := nonsymmetric_prefix_b_edge R hB hQ hd hs (carry:=nsC1 R) (by
    have h1 := pred (nsC3 R) (nsC R) (by omega)
    have hq := pred (nsP R) (nsB R) (by omega)
    have hz := pred (nsV R) (nsC R) (by omega)
    have sum := congrArg (fun n => n*nsC R) hp.2.2.2.2.2.2.2.2
    simp only [add_mul] at sum
    simp only [zero_mul,zero_add]
    have r := rel.1
    omega)
  have BC := nonsymmetric_prefix_c_edge R hB hQ hs hs' (carry:=0) (by
    have hz := pred (nsV R) (nsC R) (by omega)
    simpa only [zero_mul,add_zero,zero_add] using hz)
  have CB := nonsymmetric_prefix_b_edge R hB hQ ht hs' (carry:=nsU R) (by
    have hz := pred (nsC2 R) (nsB R) (by omega)
    simpa only [zero_mul,zero_add,add_zero] using hz.trans rel.2.1)
  rw [height0,bottom] at C
  rw [height0,side (le_refl _)] at B
  rw [side (le_refl _),side (by omega)] at BC
  rw [bottom,side (by omega)] at CB
  have B2 := B.2; have C2 := C.2; have CB2 := CB.2; have BC2 := BC.2
  dsimp only
  refine ⟨hpos,?_,?_,?_,?_,height0⟩
  · change (nonsymmetricPrefixRouting R hQ).u (gridResidue P.M.base (nsReindex R) (nsP R-1) (nsC3 R-1))=nonsymmetricDL R hB
    omega
  · change (nonsymmetricPrefixRouting R hQ).v (gridResidue P.M.base (nsReindex R) (nsP R-1) (nsC3 R-1))=nonsymmetricDL R hB
    omega
  · rw [C.1]; omega
  · rw [B.1]; omega

theorem nonsymmetric_no_right_prefix_corner_resources (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hno : ¬∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) :
    L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (nonsymmetricPrefixRouting R hQ) (nonsymmetricKappa2 R) ∧
    Nonempty (FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R) (routingHB _ _) (routingHC _ _)) := by
  have profile := nonsymmetric_no_right_prefix_corner_profile R hB hQ hno
  have hp := nonsymmetric_coefficients R
  dsimp only at profile
  constructor
  · unfold L5A2C4I.ResidueData.ExactUnusedMergeReverseBase
    rw [profile.2.1,profile.2.2.1,profile.2.2.2.1,profile.2.2.2.2.1]
    omega
  · refine ⟨⟨nonsymmetricKappa2 R,?_,?_⟩⟩
    · change (nonsymmetricPrefixRouting R hQ).u (nonsymmetricKappa2 R) ≠ 0 ∧
        (nonsymmetricPrefixRouting R hQ).v (nonsymmetricKappa2 R) ≠ 0
      rw [profile.2.1,profile.2.2.1]
      omega
    · change nonsymmetricPrefixLambda R hQ _-nsA R ∉ (nsH R).asRelativeIdeal
      have hd : NonsymmetricLDomain R (nsP R-1) (nsC3 R-1) := by unfold NonsymmetricLDomain; omega
      rw [nonsymmetric_prefix_height_formula R hB hQ hd,profile.2.2.2.2.2,Nat.cast_zero,zero_mul,zero_add]
      simpa only [Nat.cast_add,Nat.cast_mul] using nonsymmetric_canonical_a_predecessor_not_mem R hd

theorem nonsymmetric_unbalanced_no_CENTER (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hno : ¬NonsymmetricBalancedReturns R hB) :
    ¬ ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := by
  rintro ⟨ell,hi,hj⟩
  exact hno ⟨⟨ell,hi⟩,⟨ell,hj⟩⟩

theorem nonsymmetric_unbalanced_no_bad_adjacency (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hno : ¬NonsymmetricBalancedReturns R hB) :
    ∀ k, ¬NonsymmetricAdjacentBad R hB hQ k := by
  intro k hk
  by_cases hl : ∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).1 < nsP R
  · have hr : ¬∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R :=
      fun h => hno ⟨hl,h⟩
    obtain ⟨ell,he⟩ := nonsymmetric_F_source_coordinate_return R hB hQ
      (nonsymmetricFOrderedSource R hB hQ (nonsymmetricAdjacentRight R hB hQ k))
    have hx := congrArg Prod.fst he
    have hi := (nonsymmetric_no_right_return_geometry R hB hr ell).1
    change (nonsymmetricReturnTuple R hB ell).1=
      (nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentRight R hB hQ k)).1 at hx
    have hbad := hk.1
    omega
  · obtain ⟨ell,he⟩ := nonsymmetric_F_source_coordinate_return R hB hQ
      (nonsymmetricFOrderedSource R hB hQ (nonsymmetricAdjacentLeft R hB hQ k))
    have hy := congrArg Prod.snd he
    have hj := (nonsymmetric_no_left_return_geometry R hB hl ell).2
    change (nonsymmetricReturnTuple R hB ell).2.1=
      (nonsymmetricFOrderedCoordinate R hB hQ (nonsymmetricAdjacentLeft R hB hQ k)).2 at hy
    have hbad := hk.2
    omega

theorem nonsymmetric_unbalanced_notch_coverage (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hno : ¬NonsymmetricBalancedReturns R hB) :
    Nat.card (NonsymmetricPrefixFSources R hB hQ) ≤ Nat.card (NonsymmetricOrdinaryNotches R hB hQ)+1 := by
  letI : IsEmpty (NonsymmetricBadAdjacentIndices R hB hQ) :=
    ⟨fun k => nonsymmetric_unbalanced_no_bad_adjacency R hB hQ hno k.val k.property⟩
  have hc := nonsymmetric_adjacent_partition_card R hB hQ
  rw [Nat.card_of_isEmpty (α:=NonsymmetricBadAdjacentIndices R hB hQ),
    nonsymmetric_F_order_card R hB hQ] at hc
  have hp := nonsymmetric_F_order_positive R hB hQ
  rw [nonsymmetric_F_order_card R hB hQ] at hp
  have hn := nonsymmetric_adjacent_good_count_le_notches R hB hQ
  omega

theorem nonsymmetric_unbalanced_prefix_resources (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hno : ¬NonsymmetricBalancedReturns R hB) :
    Nat.card (NonsymmetricOrdinaryNotches R hB hQ)+1 ≤
      Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ)) ∧
    1 ≤ Nat.card (FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R) (routingHB _ _) (routingHC _ _)) := by
  have hex : Nonempty (NonsymmetricCornerUnusedTags R hQ) ∧
      Nonempty (FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R) (routingHB _ _) (routingHC _ _)) := by
    by_cases hl : ∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).1 < nsP R
    · have hr : ¬∃ ell : NonsymmetricReturnIndex R, (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R :=
        fun h => hno ⟨hl,h⟩
      have hc := nonsymmetric_no_right_prefix_corner_resources R hB hQ hr
      exact ⟨⟨⟨false,hc.1⟩⟩,hc.2⟩
    · have hc := nonsymmetric_no_left_prefix_corner_resources R hB hQ hl
      exact ⟨⟨⟨true,hc.1⟩⟩,hc.2⟩
  letI : Finite (L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ)) := Subtype.finite
  letI : Finite (NonsymmetricOrdinaryNotches R hB hQ) :=
    Finite.of_injective _ (nonsymmetricOrdinaryNotchResource_injective R hB hQ)
  letI : Finite (NonsymmetricCornerUnusedTags R hQ) := Subtype.finite
  letI : Nonempty (NonsymmetricCornerUnusedTags R hQ) := hex.1
  letI : Finite (FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R) (routingHB _ _) (routingHC _ _)) := Subtype.finite
  letI : Nonempty (FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R) (routingHB _ _) (routingHC _ _)) := hex.2
  have hi := Nat.card_le_card_of_injective _ (nonsymmetricPrefixUnusedResource_injective R hB hQ)
  rw [Nat.card_sum] at hi
  have hc : 0 < Nat.card (NonsymmetricCornerUnusedTags R hQ) := Nat.card_pos
  have hf : 0 < Nat.card (FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R) (routingHB _ _) (routingHC _ _)) := Nat.card_pos
  omega

theorem nonsymmetric_unbalanced_prefix_slack_bound (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hno : ¬NonsymmetricBalancedReturns R hB) : nonsymmetricPrefixSlack R hQ ≤ -1 := by
  have hc := nonsymmetric_prefix_C_count_bound R hB hQ
  have hn := nonsymmetric_unbalanced_notch_coverage R hB hQ hno
  have hres := nonsymmetric_unbalanced_prefix_resources R hB hQ hno
  have hs := nonsymmetric_prefix_raw_slack_identity R hQ
  have hz : Nat.card (NonsymmetricPrefixCenterSlot R hB)=0 := by
    rw [nonsymmetric_prefix_center_slot_count R hB,if_neg (nonsymmetric_unbalanced_no_CENTER R hB hno)]
  omega

theorem nonsymmetric_common_halfplane_actual_type_le_sourceCount (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hno : ¬NonsymmetricBalancedReturns R hB) : Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  letI : IsEmpty (NonsymmetricErasedSources R hQ) := ⟨fun s => by
    obtain ⟨ell,hi,hj,_⟩ := nonsymmetric_erased_source_is_CENTER_O R hB hQ s
    exact hno ⟨⟨ell,hi⟩,⟨ell,hj⟩⟩⟩
  have he : nonsymmetricSourceLoss R hQ=0 := Nat.card_of_isEmpty
  have hp := nonsymmetric_unbalanced_prefix_slack_bound R hB hQ hno
  have ht := nonsymmetric_DeltaSocle_le_two R hB hQ
  have hd := nonsymmetric_DeltaSource_eq_one_sub_loss R hQ
  have hw := nonsymmetric_signed_defect_identity R hQ
  rw [he,Nat.cast_zero] at hd
  rw [P2Data.W] at hw
  omega

theorem nonsymmetric_Q_gt_one_actual_type_le_sourceCount (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  by_cases hbal : NonsymmetricBalancedReturns R hB
  · exact nonsymmetric_balanced_actual_type_le_sourceCount R hB hQ hbal
  · exact nonsymmetric_common_halfplane_actual_type_le_sourceCount R hB hQ hbal

end NS25Lean.L5A2BFinalRepair
