import NS25Lean.P2BranchBPrefixOrigin

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

abbrev nonsymmetricPrefixLambda (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  (nonsymmetricPrefixIdeal R hQ).aperyRepresentative (nsA R)

/-- The six eligible entries of N4, with the zero F-quadrants included.
This is concrete arithmetic data, not a stored completeness conclusion. -/
def NonsymmetricPrefixHeightCandidate (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (x y h : ℕ) : Prop :=
  ∃ ell : NonsymmetricReturnIndex R,
    let t := nonsymmetricReturnTuple R hB ell
    (t.1 ≤ x ∧ t.2.1 ≤ y ∧ h=0) ∨
    (t.1 < nsP R ∧ t.2.1 < nsQ R ∧ h=nsC1 R-t.2.2) ∨
    (nsP R ≤ t.1 ∧ t.1-nsP R ≤ x ∧ h=nsC1 R-t.2.2) ∨
    (nsQ R ≤ t.2.1 ∧ t.2.1-nsQ R ≤ y ∧ h=nsC1 R-t.2.2) ∨
    (t.1 < nsP R ∧ t.1+nsZ R ≤ x ∧ h=nsW R-t.2.2) ∨
    (t.2.1 < nsQ R ∧ t.2.1+nsV R ≤ y ∧ h=nsU R-t.2.2)

theorem nonsymmetric_grid_ideal_coordinates_mono (R : SectorBCriticalRoleBranchB P)
    (I : RelativeIdeal (nsH R)) {h x y h' x' y' : ℕ}
    (hm : ((h*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ) ∈ I)
    (hh : h ≤ h') (hx : x ≤ x') (hy : y ≤ y') :
    ((h'*nsA R+x'*nsB R+y'*nsC R : ℕ) : ℤ) ∈ I := by
  obtain ⟨w,hw,he⟩ := nonsymmetric_grid_mem R (h'-h) (x'-x) (y'-y)
  have hadd := I.add_mem hm hw
  have h1 := congrArg (fun n => n*nsA R) (Nat.sub_add_cancel hh)
  have h2 := congrArg (fun n => n*nsB R) (Nat.sub_add_cancel hx)
  have h3 := congrArg (fun n => n*nsC R) (Nat.sub_add_cancel hy)
  simp only [add_mul] at h1 h2 h3
  have hval : h'*nsA R+x'*nsB R+y'*nsC R=
      h*nsA R+x*nsB R+y*nsC R+((h'-h)*nsA R+(x'-x)*nsB R+(y'-y)*nsC R) := by omega
  rw [← he] at hadd
  change ((h'*nsA R+x'*nsB R+y'*nsC R : ℕ) : ℤ) ∈ I.carrier
  rw [hval]
  simpa only [Nat.cast_add] using hadd

theorem nonsymmetric_prefix_height_candidate_mem (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    {x y h : ℕ} (hc : NonsymmetricPrefixHeightCandidate R hB x y h) :
    ((h*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ) ∈ nonsymmetricPrefixIdeal R hQ := by
  obtain ⟨ell,hc⟩ := hc
  let t := nonsymmetricReturnTuple R hB ell
  have S := nonsymmetricReturnTuple_spec R hB ell
  have hm := nonsymmetric_single_return_sources_mem R hB ell.property.1 S.1 S.2.2.2.2.2.2
  have toPrefix (z : ℤ) (hz : z ∈ returnIdeal (nsH R) (ell.val*normalizedM P.M.base)) :
      z ∈ nonsymmetricPrefixIdeal R hQ := ⟨ell.val,ell.property.1,ell.property.2,hz⟩
  rcases hc with ⟨hi,hj,rfl⟩ | ⟨hi,hj,rfl⟩ | ⟨hi,hx,rfl⟩ |
    ⟨hj,hy,rfl⟩ | ⟨hi,hx,rfl⟩ | ⟨hj,hy,rfl⟩
  · apply nonsymmetric_grid_ideal_coordinates_mono R _ (h:=0) (x:=t.1) (y:=t.2.1) _ (le_refl _) hi hj
    simpa only [zero_mul,zero_add] using toPrefix _ hm.1
  · apply nonsymmetric_grid_ideal_coordinates_mono R _ (x:=0) (y:=0) _ (le_refl _) (Nat.zero_le _) (Nat.zero_le _)
    simpa only [zero_mul,add_zero] using toPrefix _ (hm.2.2.2 hi hj)
  · apply nonsymmetric_grid_ideal_coordinates_mono R _ (x:=t.1-nsP R) (y:=0) _ (le_refl _) hx (Nat.zero_le _)
    have hnot : ¬ (nonsymmetricReturnTuple R hB ell).1 < nsP R := by omega
    simpa only [nonsymmetricX,ite_eq_right hnot,zero_mul,add_zero] using toPrefix _ hm.2.1
  · apply nonsymmetric_grid_ideal_coordinates_mono R _ (x:=0) (y:=t.2.1-nsQ R) _ (le_refl _) (Nat.zero_le _) hy
    have hnot : ¬ (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := by omega
    simpa only [nonsymmetricY,ite_eq_right hnot,zero_mul,add_zero] using toPrefix _ hm.2.2.1
  · apply nonsymmetric_grid_ideal_coordinates_mono R _ (x:=t.1+nsZ R) (y:=0) _ (le_refl _) hx (Nat.zero_le _)
    simpa only [nonsymmetricX,ite_eq_left hi,zero_mul,add_zero] using toPrefix _ hm.2.1
  · apply nonsymmetric_grid_ideal_coordinates_mono R _ (x:=0) (y:=t.2.1+nsV R) _ (le_refl _) (Nat.zero_le _) hy
    simpa only [nonsymmetricY,ite_eq_left hj,zero_mul,add_zero] using toPrefix _ hm.2.2.1

theorem nonsymmetric_prefix_height_candidate_nonempty (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (x y : ℕ) :
    Nonempty {h : ℕ // NonsymmetricPrefixHeightCandidate R hB x y h} := by
  obtain ⟨ell,hi,hj⟩ := nonsymmetric_inclusive_origin_return R hB hQ
  refine ⟨⟨nsC1 R-(nonsymmetricReturnTuple R hB ell).2.2,ell,?_⟩⟩
  by_cases hip : (nonsymmetricReturnTuple R hB ell).1 < nsP R
  · by_cases hjq : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R
    · exact Or.inr (Or.inl ⟨hip,hjq,rfl⟩)
    · right; right; right; left
      exact ⟨by omega,by omega,rfl⟩
  · right; right; left
    exact ⟨by omega,by omega,rfl⟩

def nonsymmetricPrefixDiagramHeight (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (x y : ℕ) : ℕ :=
  natMinImage (nonsymmetric_prefix_height_candidate_nonempty R hB hQ x y) Subtype.val

theorem nonsymmetric_prefix_diagram_height_attained (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (x y : ℕ) :
    NonsymmetricPrefixHeightCandidate R hB x y (nonsymmetricPrefixDiagramHeight R hB hQ x y) := by
  obtain ⟨h,he⟩ := natMinImage_spec (nonsymmetric_prefix_height_candidate_nonempty R hB hQ x y) Subtype.val
  rw [nonsymmetricPrefixDiagramHeight,← he]
  exact h.property

theorem nonsymmetric_prefix_diagram_grid_mem (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (x y : ℕ) :
    ((nonsymmetricPrefixDiagramHeight R hB hQ x y*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ) ∈ nonsymmetricPrefixIdeal R hQ :=
  nonsymmetric_prefix_height_candidate_mem R hB hQ (nonsymmetric_prefix_diagram_height_attained R hB hQ x y)

theorem nonsymmetric_prefix_height_candidate_lt_c1 (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {x y h : ℕ} (hc : NonsymmetricPrefixHeightCandidate R hB x y h) : h < nsC1 R := by
  obtain ⟨ell,hc⟩ := hc
  have S := nonsymmetricReturnTuple_spec R hB ell
  have hd := nonsymmetric_return_depth_lt_c1 R hB ell.property.1 S.1 S.2.2.2.2.2.2
  have hp := nonsymmetric_coefficients R
  rcases hc with ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ <;> omega

theorem nonsymmetric_prefix_diagram_height_lt_c1 (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (x y : ℕ) :
    nonsymmetricPrefixDiagramHeight R hB hQ x y < nsC1 R :=
  nonsymmetric_prefix_height_candidate_lt_c1 R hB (nonsymmetric_prefix_diagram_height_attained R hB hQ x y)

theorem nonsymmetric_prefix_height_candidate_zero_iff (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (x y : ℕ) :
    NonsymmetricPrefixHeightCandidate R hB x y 0 ↔
    ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 ≤ x ∧ (nonsymmetricReturnTuple R hB ell).2.1 ≤ y := by
  constructor
  · rintro ⟨ell,hc⟩
    have S := nonsymmetricReturnTuple_spec R hB ell
    have hd := nonsymmetric_return_depth_lt_c1 R hB ell.property.1 S.1 S.2.2.2.2.2.2
    rcases hc with ⟨hi,hj,_⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨hi,_,he⟩ | ⟨hj,_,he⟩
    · exact ⟨ell,hi,hj⟩
    · omega
    · omega
    · omega
    · have := S.2.2.2.2.1 hi; omega
    · have := S.2.2.2.2.2.1 hj; omega
  · rintro ⟨ell,hi,hj⟩
    exact ⟨ell,Or.inl ⟨hi,hj,rfl⟩⟩

theorem nonsymmetric_prefix_diagram_height_zero_iff (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (x y : ℕ) :
    nonsymmetricPrefixDiagramHeight R hB hQ x y=0 ↔
    ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 ≤ x ∧ (nonsymmetricReturnTuple R hB ell).2.1 ≤ y := by
  constructor
  · intro he
    have hm := nonsymmetric_prefix_diagram_height_attained R hB hQ x y
    rw [he] at hm
    exact (nonsymmetric_prefix_height_candidate_zero_iff R hB x y).mp hm
  · intro hm
    have hc := (nonsymmetric_prefix_height_candidate_zero_iff R hB x y).mpr hm
    have hl := natMinImage_le (nonsymmetric_prefix_height_candidate_nonempty R hB hQ x y) Subtype.val ⟨0,hc⟩
    change nonsymmetricPrefixDiagramHeight R hB hQ x y ≤ 0 at hl
    omega

theorem nonsymmetric_prefix_lambda_le_diagram (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (x y : ℕ) :
    nonsymmetricPrefixLambda R hQ (gridResidue P.M.base (nsReindex R) x y) ≤
      (nonsymmetricPrefixDiagramHeight R hB hQ x y : ℤ)*nsA R+x*nsB R+y*nsC R := by
  have hm := nonsymmetric_prefix_diagram_grid_mem R hB hQ x y
  have hmod := normalizedGrid_mod P.M.base (nsReindex R) (nonsymmetricPrefixDiagramHeight R hB hQ x y) x y
  have hl := (nonsymmetricPrefixIdeal R hQ).aperyRepresentative_le (nsA R) _ hm
    (by simpa only [normalizedGrid,Int.cast_natCast] using hmod)
  simpa only [Nat.cast_add,Nat.cast_mul] using hl

theorem nonsymmetric_prefix_diagram_le_candidate (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {x y h : ℕ}
    (hc : NonsymmetricPrefixHeightCandidate R hB x y h) :
    nonsymmetricPrefixDiagramHeight R hB hQ x y ≤ h :=
  natMinImage_le (nonsymmetric_prefix_height_candidate_nonempty R hB hQ x y)
    Subtype.val ⟨h,hc⟩

theorem nonsymmetric_prefix_height_candidate_mono (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) {x y x' y' h : ℕ}
    (hc : NonsymmetricPrefixHeightCandidate R hB x y h) (hx : x ≤ x') (hy : y ≤ y') :
    NonsymmetricPrefixHeightCandidate R hB x' y' h := by
  obtain ⟨ell,hc⟩ := hc
  refine ⟨ell,?_⟩
  rcases hc with ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩ |
    ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩
  · exact Or.inl ⟨by omega,by omega,he⟩
  · exact Or.inr (Or.inl ⟨hi,hj,he⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hi,by omega,he⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,by omega,he⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,by omega,he⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hi,by omega,he⟩))))

theorem nonsymmetric_prefix_diagram_antitone (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {x y x' y' : ℕ}
    (hx : x ≤ x') (hy : y ≤ y') :
    nonsymmetricPrefixDiagramHeight R hB hQ x' y' ≤ nonsymmetricPrefixDiagramHeight R hB hQ x y :=
  nonsymmetric_prefix_diagram_le_candidate R hB hQ
    (nonsymmetric_prefix_height_candidate_mono R hB
      (nonsymmetric_prefix_diagram_height_attained R hB hQ x y) hx hy)

theorem nonsymmetric_prefix_diagram_outer_b (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {y : ℕ} (hy : y < nsQ R) :
    nonsymmetricPrefixDiagramHeight R hB hQ 0 (y+nsV R) ≤
      nonsymmetricPrefixDiagramHeight R hB hQ (nsC2 R-1) y+nsU R := by
  obtain ⟨ell,hc⟩ := nonsymmetric_prefix_diagram_height_attained R hB hQ (nsC2 R-1) y
  have S := nonsymmetricReturnTuple_spec R hB ell
  have hp := nonsymmetric_coefficients R
  have hd := nonsymmetric_return_depth_lt_c1 R hB ell.property.1 S.1 S.2.2.2.2.2.2
  have upper := nonsymmetric_prefix_diagram_height_lt_c1 R hB hQ 0 (y+nsV R)
  have dom := S.1
  unfold NonsymmetricLDomain at dom
  have bound {h : ℕ} (hc : NonsymmetricPrefixHeightCandidate R hB 0 (y+nsV R) h) :=
    nonsymmetric_prefix_diagram_le_candidate R hB hQ hc
  rcases hc with ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,hx,he⟩ |
    ⟨hj,hy',he⟩ | ⟨hi,hx,he⟩ | ⟨hj,hy',he⟩
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨by omega,by omega,rfl⟩))))⟩
    omega
  · have hl := bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩
    omega
  · have hj : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := by
      rcases S.1.2.2 with h | h <;> omega
    have hb := S.2.2.2.2.2.1 hj
    omega
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inl ⟨hj,by omega,rfl⟩)))⟩
    omega
  · have hb := S.2.2.2.2.1 hi
    by_cases hj : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R
    · have hl := bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩
      omega
    · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,rfl⟩)))⟩
      omega
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hj,by omega,rfl⟩))))⟩
    omega

theorem nonsymmetric_prefix_diagram_outer_c (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {x : ℕ} (hx : x < nsP R) :
    nonsymmetricPrefixDiagramHeight R hB hQ (x+nsZ R) 0 ≤
      nonsymmetricPrefixDiagramHeight R hB hQ x (nsC3 R-1)+nsW R := by
  obtain ⟨ell,hc⟩ := nonsymmetric_prefix_diagram_height_attained R hB hQ x (nsC3 R-1)
  have S := nonsymmetricReturnTuple_spec R hB ell
  have hp := nonsymmetric_coefficients R
  have hd := nonsymmetric_return_depth_lt_c1 R hB ell.property.1 S.1 S.2.2.2.2.2.2
  have upper := nonsymmetric_prefix_diagram_height_lt_c1 R hB hQ (x+nsZ R) 0
  have dom := S.1
  unfold NonsymmetricLDomain at dom
  have bound {h : ℕ} (hc : NonsymmetricPrefixHeightCandidate R hB (x+nsZ R) 0 h) :=
    nonsymmetric_prefix_diagram_le_candidate R hB hQ hc
  rcases hc with ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,hx',he⟩ |
    ⟨hj,hy,he⟩ | ⟨hi,hx',he⟩ | ⟨hj,hy,he⟩
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega,by omega,rfl⟩))))⟩
    omega
  · have hl := bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩
    omega
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inl ⟨hi,by omega,rfl⟩))⟩
    omega
  · have hi : (nonsymmetricReturnTuple R hB ell).1 < nsP R := by
      rcases S.1.2.2 with h | h <;> omega
    have hb := S.2.2.2.2.1 hi
    omega
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,by omega,rfl⟩))))⟩
    omega
  · have hb := S.2.2.2.2.2.1 hj
    by_cases hi : (nonsymmetricReturnTuple R hB ell).1 < nsP R
    · have hl := bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩
      omega
    · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inl ⟨by omega,by omega,rfl⟩))⟩
      omega

end NS25Lean.L5A2BFinalRepair
