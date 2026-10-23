import NS25Lean.P2BranchBPrefixHeightClosure

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

theorem nonsymmetric_depth_le_max (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    {p : NonsymmetricReturnIndex R → Prop} (ell : NonsymmetricReturnIndex R) (he : p ell) :
    (nonsymmetricReturnTuple R hB ell).2.2 ≤ nonsymmetricReturnDepthMax R hB p := by
  letI := nonsymmetricReturnIndex_finite R
  letI := Fintype.ofFinite (NonsymmetricReturnIndex R)
  unfold nonsymmetricReturnDepthMax
  simpa only [ite_eq_left he] using
    (Finset.le_sup (f:=fun ell => if p ell then (nonsymmetricReturnTuple R hB ell).2.2 else 0)
      (Finset.mem_univ ell))

theorem nonsymmetric_depth_max_lt (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    {p : NonsymmetricReturnIndex R → Prop} {n : ℕ} (hn : 0 < n)
    (hb : ∀ ell, p ell → (nonsymmetricReturnTuple R hB ell).2.2 < n) :
    nonsymmetricReturnDepthMax R hB p < n := by
  letI := nonsymmetricReturnIndex_finite R
  letI := Fintype.ofFinite (NonsymmetricReturnIndex R)
  have he : nonsymmetricReturnDepthMax R hB p ≤ n-1 := by
    unfold nonsymmetricReturnDepthMax
    apply Finset.sup_le
    intro ell hell
    split_ifs with hp
    · have := hb ell hp; omega
    · omega
  omega

theorem nonsymmetric_depth_max_attained (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    {p : NonsymmetricReturnIndex R → Prop} (hp : ∃ ell, p ell) :
    ∃ ell, p ell ∧ (nonsymmetricReturnTuple R hB ell).2.2=nonsymmetricReturnDepthMax R hB p := by
  letI := nonsymmetricReturnIndex_finite R
  letI := Fintype.ofFinite (NonsymmetricReturnIndex R)
  obtain ⟨ell0,h0⟩ := hp
  have hpos : 0 < nonsymmetricReturnDepthMax R hB p :=
    lt_of_lt_of_le (nonsymmetricReturnTuple_spec R hB ell0).2.2.2.1
      (nonsymmetric_depth_le_max R hB ell0 h0)
  have hex : ∃ ell ∈ Finset.univ, (if p ell then (nonsymmetricReturnTuple R hB ell).2.2 else 0)=
      nonsymmetricReturnDepthMax R hB p := by
    obtain ⟨ell,hell,he⟩ := Finset.exists_mem_eq_sup Finset.univ
      (show (Finset.univ : Finset (NonsymmetricReturnIndex R)).Nonempty from
        ⟨ell0,Finset.mem_univ ell0⟩)
      (fun ell => if p ell then (nonsymmetricReturnTuple R hB ell).2.2 else 0)
    exact ⟨ell,hell,he.symm⟩
  obtain ⟨ell,_,he⟩ := hex
  by_cases hp' : p ell
  · exact ⟨ell,hp',by simpa only [ite_eq_left hp'] using he⟩
  · simp only [ite_eq_right hp'] at he; omega

theorem nonsymmetric_balanced_depth_maxima (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hbal : NonsymmetricBalancedReturns R hB) :
    0 < nonsymmetricDL R hB ∧ nonsymmetricDL R hB < nsW R ∧
    0 < nonsymmetricDR R hB ∧ nonsymmetricDR R hB < nsU R := by
  have hp := nonsymmetric_coefficients R
  obtain ⟨l,hl⟩ := hbal.1
  obtain ⟨r,hr⟩ := hbal.2
  refine ⟨lt_of_lt_of_le (nonsymmetricReturnTuple_spec R hB l).2.2.2.1
    (nonsymmetric_depth_le_max R hB l hl),?_,
    lt_of_lt_of_le (nonsymmetricReturnTuple_spec R hB r).2.2.2.1
    (nonsymmetric_depth_le_max R hB r hr),?_⟩
  · exact nonsymmetric_depth_max_lt R hB hp.2.2.2.2.1
      (fun ell => (nonsymmetricReturnTuple_spec R hB ell).2.2.2.2.1)
  · exact nonsymmetric_depth_max_lt R hB hp.2.2.1
      (fun ell => (nonsymmetricReturnTuple_spec R hB ell).2.2.2.2.2.1)

theorem nonsymmetric_prefix_corner1_height_zero (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    nonsymmetricPrefixDiagramHeight R hB hQ (nsC2 R-1) (nsQ R-1)=0 := by
  obtain ⟨ell,hj⟩ := hbal.2
  have S := nonsymmetricReturnTuple_spec R hB ell
  have dom := S.1; unfold NonsymmetricLDomain at dom
  apply (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mpr
  exact ⟨ell,by omega,by omega⟩

theorem nonsymmetric_prefix_corner2_height_zero (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    nonsymmetricPrefixDiagramHeight R hB hQ (nsP R-1) (nsC3 R-1)=0 := by
  obtain ⟨ell,hi⟩ := hbal.1
  have S := nonsymmetricReturnTuple_spec R hB ell
  have dom := S.1; unfold NonsymmetricLDomain at dom
  apply (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mpr
  exact ⟨ell,by omega,by omega⟩

theorem nonsymmetric_prefix_left_top_height (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    nonsymmetricPrefixDiagramHeight R hB hQ 0 (nsC3 R-1)=nsU R-nonsymmetricDR R hB := by
  have hp := nonsymmetric_coefficients R
  have maxima := nonsymmetric_balanced_depth_maxima R hB hbal
  apply le_antisymm
  · obtain ⟨ell,hj,he⟩ := nonsymmetric_depth_max_attained R hB hbal.2
    have hc : NonsymmetricPrefixHeightCandidate R hB 0 (nsC3 R-1)
        (nsU R-nonsymmetricDR R hB) := by
      refine ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hj,by omega,?_⟩))))⟩
      rw [he]
    exact nonsymmetric_prefix_diagram_le_candidate R hB hQ hc
  · obtain ⟨ell,hc⟩ := nonsymmetric_prefix_diagram_height_attained R hB hQ 0 (nsC3 R-1)
    have S := nonsymmetricReturnTuple_spec R hB ell
    rcases hc with ⟨hi,_,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,hx,he⟩ |
      ⟨hj,_,he⟩ | ⟨hi,hx,he⟩ | ⟨hj,_,he⟩
    · omega
    · have hb := S.2.2.2.2.1 hi; omega
    · have hj : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := by
        rcases S.1.2.2 with h | h <;> omega
      have hd := nonsymmetric_depth_le_max R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).2.1 < nsQ R) ell hj
      change _ ≤ nonsymmetricDR R hB at hd
      omega
    · have hi : (nonsymmetricReturnTuple R hB ell).1 < nsP R := by
        rcases S.1.2.2 with h | h <;> omega
      have hb := S.2.2.2.2.1 hi; omega
    · omega
    · have hd := nonsymmetric_depth_le_max R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).2.1 < nsQ R) ell hj
      change _ ≤ nonsymmetricDR R hB at hd
      omega

theorem nonsymmetric_prefix_bottom_right_height (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    nonsymmetricPrefixDiagramHeight R hB hQ (nsC2 R-1) 0=nsW R-nonsymmetricDL R hB := by
  have hp := nonsymmetric_coefficients R
  have maxima := nonsymmetric_balanced_depth_maxima R hB hbal
  apply le_antisymm
  · obtain ⟨ell,hi,he⟩ := nonsymmetric_depth_max_attained R hB hbal.1
    have hc : NonsymmetricPrefixHeightCandidate R hB (nsC2 R-1) 0
        (nsW R-nonsymmetricDL R hB) := by
      refine ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,by omega,?_⟩))))⟩
      rw [he]
    exact nonsymmetric_prefix_diagram_le_candidate R hB hQ hc
  · obtain ⟨ell,hc⟩ := nonsymmetric_prefix_diagram_height_attained R hB hQ (nsC2 R-1) 0
    have S := nonsymmetricReturnTuple_spec R hB ell
    rcases hc with ⟨_,hj,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,_,he⟩ |
      ⟨hj,hy,he⟩ | ⟨hi,_,he⟩ | ⟨hj,hy,he⟩
    · omega
    · have hb := S.2.2.2.2.2.1 hj; omega
    · have hj : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := by
        rcases S.1.2.2 with h | h <;> omega
      have hb := S.2.2.2.2.2.1 hj; omega
    · have hi : (nonsymmetricReturnTuple R hB ell).1 < nsP R := by
        rcases S.1.2.2 with h | h <;> omega
      have hd := nonsymmetric_depth_le_max R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).1 < nsP R) ell hi
      change _ ≤ nonsymmetricDL R hB at hd
      omega
    · have hd := nonsymmetric_depth_le_max R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).1 < nsP R) ell hi
      change _ ≤ nonsymmetricDL R hB at hd
      omega
    · omega

theorem nonsymmetric_depth_max_positive_witness (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {p : NonsymmetricReturnIndex R → Prop}
    (hp : 0 < nonsymmetricReturnDepthMax R hB p) : ∃ ell, p ell := by
  by_contra hn
  have he : nonsymmetricReturnDepthMax R hB p=0 := by
    letI := nonsymmetricReturnIndex_finite R
    letI := Fintype.ofFinite (NonsymmetricReturnIndex R)
    unfold nonsymmetricReturnDepthMax
    apply le_antisymm
    · apply Finset.sup_le
      intro ell hell
      simp only [ite_eq_right (show ¬ p ell from fun he => hn ⟨ell,he⟩)]
      exact le_refl _
    · exact Nat.zero_le _
  omega

theorem nonsymmetric_prefix_bottom_seam_height (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) {x : ℕ} (hx : nsZ R-1 ≤ x) (hx' : x ≤ nsZ R) :
    nonsymmetricPrefixDiagramHeight R hB hQ x 0=
      nsC1 R-max (nonsymmetricDR R hB) (nonsymmetricDL0 R hB) := by
  have hp := nonsymmetric_coefficients R
  have maxima := nonsymmetric_balanced_depth_maxima R hB hbal
  have bh := nonsymmetric_boundary_depth_maxima_le R hB
  have bound {h : ℕ} (hc : NonsymmetricPrefixHeightCandidate R hB x 0 h) :=
    nonsymmetric_prefix_diagram_le_candidate R hB hQ hc
  apply le_antisymm
  · by_cases hm : nonsymmetricDL0 R hB ≤ nonsymmetricDR R hB
    · rw [max_eq_left hm]
      obtain ⟨ell,hj,he⟩ := nonsymmetric_depth_max_attained R hB hbal.2
      have S := nonsymmetricReturnTuple_spec R hB ell
      have dom := S.1; unfold NonsymmetricLDomain at dom
      by_cases hi : (nonsymmetricReturnTuple R hB ell).1 < nsP R
      · have hb := bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩
        rw [he] at hb; exact hb
      · have hb := bound ⟨ell,Or.inr (Or.inr (Or.inl ⟨by omega,by omega,rfl⟩))⟩
        rw [he] at hb; exact hb
    · have hm' : nonsymmetricDR R hB ≤ nonsymmetricDL0 R hB := by omega
      rw [max_eq_right hm']
      have hex := nonsymmetric_depth_max_positive_witness R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).2.1=nsQ R)
        (by change 0 < nonsymmetricDL0 R hB; omega)
      obtain ⟨ell,hj,he⟩ := nonsymmetric_depth_max_attained R hB hex
      have hb := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,rfl⟩)))⟩
      rw [he] at hb; exact hb
  · obtain ⟨ell,hc⟩ := nonsymmetric_prefix_diagram_height_attained R hB hQ x 0
    have S := nonsymmetricReturnTuple_spec R hB ell
    have M1 := le_max_left (nonsymmetricDR R hB) (nonsymmetricDL0 R hB)
    have M2 := le_max_right (nonsymmetricDR R hB) (nonsymmetricDL0 R hB)
    rcases hc with ⟨_,hj,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,_,he⟩ |
      ⟨hj,hy,he⟩ | ⟨hi,hx'',he⟩ | ⟨hj,hy,he⟩
    · omega
    · have hd := nonsymmetric_depth_le_max R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).2.1 < nsQ R) ell hj
      change _ ≤ nonsymmetricDR R hB at hd
      omega
    · have hj : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := by
        rcases S.1.2.2 with h | h <;> omega
      have hd := nonsymmetric_depth_le_max R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).2.1 < nsQ R) ell hj
      change _ ≤ nonsymmetricDR R hB at hd
      omega
    · have hj' : (nonsymmetricReturnTuple R hB ell).2.1=nsQ R := by omega
      have hd := nonsymmetric_depth_le_max R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).2.1=nsQ R) ell hj'
      change _ ≤ nonsymmetricDL0 R hB at hd
      omega
    · omega
    · omega

theorem nonsymmetric_prefix_left_seam_height (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) {y : ℕ} (hy : nsV R-1 ≤ y) (hy' : y ≤ nsV R) :
    nonsymmetricPrefixDiagramHeight R hB hQ 0 y=
      nsC1 R-max (nonsymmetricDL R hB) (nonsymmetricDR0 R hB) := by
  have hp := nonsymmetric_coefficients R
  have maxima := nonsymmetric_balanced_depth_maxima R hB hbal
  have bh := nonsymmetric_boundary_depth_maxima_le R hB
  have bound {h : ℕ} (hc : NonsymmetricPrefixHeightCandidate R hB 0 y h) :=
    nonsymmetric_prefix_diagram_le_candidate R hB hQ hc
  apply le_antisymm
  · by_cases hm : nonsymmetricDR0 R hB ≤ nonsymmetricDL R hB
    · rw [max_eq_left hm]
      obtain ⟨ell,hi,he⟩ := nonsymmetric_depth_max_attained R hB hbal.1
      have S := nonsymmetricReturnTuple_spec R hB ell
      have dom := S.1; unfold NonsymmetricLDomain at dom
      by_cases hj : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R
      · have hb := bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩
        rw [he] at hb; exact hb
      · have hb := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,rfl⟩)))⟩
        rw [he] at hb; exact hb
    · have hm' : nonsymmetricDL R hB ≤ nonsymmetricDR0 R hB := by omega
      rw [max_eq_right hm']
      have hex := nonsymmetric_depth_max_positive_witness R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).1=nsP R)
        (by change 0 < nonsymmetricDR0 R hB; omega)
      obtain ⟨ell,hi,he⟩ := nonsymmetric_depth_max_attained R hB hex
      have hb := bound ⟨ell,Or.inr (Or.inr (Or.inl ⟨by omega,by omega,rfl⟩))⟩
      rw [he] at hb; exact hb
  · obtain ⟨ell,hc⟩ := nonsymmetric_prefix_diagram_height_attained R hB hQ 0 y
    have S := nonsymmetricReturnTuple_spec R hB ell
    have M1 := le_max_left (nonsymmetricDL R hB) (nonsymmetricDR0 R hB)
    have M2 := le_max_right (nonsymmetricDL R hB) (nonsymmetricDR0 R hB)
    rcases hc with ⟨hi,_,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,hx,he⟩ |
      ⟨hj,_,he⟩ | ⟨hi,hx,he⟩ | ⟨hj,hy'',he⟩
    · omega
    · have hd := nonsymmetric_depth_le_max R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).1 < nsP R) ell hi
      change _ ≤ nonsymmetricDL R hB at hd
      omega
    · have hi' : (nonsymmetricReturnTuple R hB ell).1=nsP R := by omega
      have hd := nonsymmetric_depth_le_max R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).1=nsP R) ell hi'
      change _ ≤ nonsymmetricDR0 R hB at hd
      omega
    · have hi : (nonsymmetricReturnTuple R hB ell).1 < nsP R := by
        rcases S.1.2.2 with h | h <;> omega
      have hd := nonsymmetric_depth_le_max R hB
        (p:=fun k => (nonsymmetricReturnTuple R hB k).1 < nsP R) ell hi
      change _ ≤ nonsymmetricDL R hB at hd
      omega
    · omega
    · omega

end NS25Lean.L5A2BFinalRepair
