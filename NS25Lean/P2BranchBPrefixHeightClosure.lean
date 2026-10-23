import NS25Lean.P2BranchBPrefixHeight

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Canonical L-shape values at or above the concrete N4 diagram. -/
def NonsymmetricPrefixDiagramMember (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (s : ℕ) : Prop :=
  ∃ h x y, NonsymmetricLDomain R x y ∧
    nonsymmetricPrefixDiagramHeight R hB hQ x y ≤ h ∧
    s=h*nsA R+x*nsB R+y*nsC R

theorem nonsymmetric_prefix_diagram_add_a (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {s : ℕ}
    (hs : NonsymmetricPrefixDiagramMember R hB hQ s) :
    NonsymmetricPrefixDiagramMember R hB hQ (s+nsA R) := by
  obtain ⟨h,x,y,hd,hh,rfl⟩ := hs
  refine ⟨h+1,x,y,hd,by omega,?_⟩
  simp only [add_mul,one_mul]; omega

theorem nonsymmetric_prefix_diagram_add_b (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {s : ℕ}
    (hs : NonsymmetricPrefixDiagramMember R hB hQ s) :
    NonsymmetricPrefixDiagramMember R hB hQ (s+nsB R) := by
  obtain ⟨h,x,y,hd,hh,rfl⟩ := hs
  have hp := nonsymmetric_coefficients R
  have hr := nonsymmetric_normalized_relations R
  unfold NonsymmetricLDomain at hd
  by_cases hn : x+1 < nsC2 R ∧ (x+1 < nsP R ∨ y < nsQ R)
  · refine ⟨h,x+1,y,⟨hn.1,hd.2.1,hn.2⟩,?_,?_⟩
    · exact le_trans (nonsymmetric_prefix_diagram_antitone R hB hQ (by omega) (le_refl _)) hh
    · simp only [add_mul,one_mul]; omega
  · by_cases hy : nsQ R ≤ y
    · have hx : x+1=nsP R := by rcases hd.2.2 with h | h <;> omega
      have hy' : y-nsQ R < nsC3 R := by omega
      have hdom : NonsymmetricLDomain R 0 (y-nsQ R) := ⟨by omega,hy',Or.inl hp.1⟩
      have hb := nonsymmetric_prefix_diagram_height_lt_c1 R hB hQ 0 (y-nsQ R)
      refine ⟨h+nsC1 R,0,y-nsQ R,hdom,by omega,?_⟩
      have hyEq := congrArg (fun n => n*nsC R) (Nat.sub_add_cancel hy)
      have hxEq := congrArg (fun n => n*nsB R) hx
      simp only [add_mul,one_mul,zero_mul,add_zero,zero_add] at *
      omega
    · have hx : x+1=nsC2 R := by omega
      have hdom : NonsymmetricLDomain R 0 (y+nsV R) := ⟨by omega,by omega,Or.inl hp.1⟩
      have hx' : x=nsC2 R-1 := by omega
      have hb := nonsymmetric_prefix_diagram_outer_b R hB hQ (by omega : y < nsQ R)
      rw [← hx'] at hb
      refine ⟨h+nsU R,0,y+nsV R,hdom,by omega,?_⟩
      have hxEq := congrArg (fun n => n*nsB R) hx
      simp only [add_mul,one_mul,zero_mul,add_zero,zero_add] at *
      omega

theorem nonsymmetric_prefix_diagram_add_c (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {s : ℕ}
    (hs : NonsymmetricPrefixDiagramMember R hB hQ s) :
    NonsymmetricPrefixDiagramMember R hB hQ (s+nsC R) := by
  obtain ⟨h,x,y,hd,hh,rfl⟩ := hs
  have hp := nonsymmetric_coefficients R
  have hr := nonsymmetric_normalized_relations R
  unfold NonsymmetricLDomain at hd
  by_cases hn : y+1 < nsC3 R ∧ (x < nsP R ∨ y+1 < nsQ R)
  · refine ⟨h,x,y+1,⟨hd.1,hn.1,hn.2⟩,?_,?_⟩
    · exact le_trans (nonsymmetric_prefix_diagram_antitone R hB hQ (le_refl _) (by omega)) hh
    · simp only [add_mul,one_mul]; omega
  · by_cases hx : nsP R ≤ x
    · have hy : y+1=nsQ R := by rcases hd.2.2 with h | h <;> omega
      have hdom : NonsymmetricLDomain R (x-nsP R) 0 := ⟨by omega,by omega,Or.inr hp.2.1⟩
      have hb := nonsymmetric_prefix_diagram_height_lt_c1 R hB hQ (x-nsP R) 0
      refine ⟨h+nsC1 R,x-nsP R,0,hdom,by omega,?_⟩
      have hxEq := congrArg (fun n => n*nsB R) (Nat.sub_add_cancel hx)
      have hyEq := congrArg (fun n => n*nsC R) hy
      simp only [add_mul,one_mul,zero_mul,add_zero,zero_add] at *
      omega
    · have hy : y+1=nsC3 R := by omega
      have hdom : NonsymmetricLDomain R (x+nsZ R) 0 := ⟨by omega,by omega,Or.inr hp.2.1⟩
      have hy' : y=nsC3 R-1 := by omega
      have hb := nonsymmetric_prefix_diagram_outer_c R hB hQ (by omega : x < nsP R)
      rw [← hy'] at hb
      refine ⟨h+nsW R,x+nsZ R,0,hdom,by omega,?_⟩
      have hyEq := congrArg (fun n => n*nsC R) hy
      simp only [add_mul,one_mul,zero_mul,add_zero,zero_add] at *
      omega

private theorem add_multiples {K : ℕ → Prop} {g s : ℕ}
    (step : ∀ z, K z → K (z+g)) (hs : K s) (n : ℕ) : K (s+n*g) := by
  induction n with
  | zero => simpa using hs
  | succ n ih => simpa only [Nat.succ_mul,← add_assoc] using step _ ih

theorem nonsymmetric_prefix_diagram_add_tail (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {s w : ℕ}
    (hs : NonsymmetricPrefixDiagramMember R hB hQ s) (hw : w ∈ nsH R) :
    NonsymmetricPrefixDiagramMember R hB hQ (s+w) := by
  obtain ⟨t,x,y,he⟩ := L5A2C4OR6.routingH_factorization P.M.base (nsReindex R) hw
  change w=t*nsA R+x*nsB R+y*nsC R at he
  have ha := add_multiples (fun _ => nonsymmetric_prefix_diagram_add_a R hB hQ) hs t
  have hb := add_multiples (fun _ => nonsymmetric_prefix_diagram_add_b R hB hQ) ha x
  have hc := add_multiples (fun _ => nonsymmetric_prefix_diagram_add_c R hB hQ) hb y
  simpa only [he,add_assoc] using hc

theorem nonsymmetric_prefix_source_diagram_members (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ell : NonsymmetricReturnIndex R) :
    let t := nonsymmetricReturnTuple R hB ell
    NonsymmetricPrefixDiagramMember R hB hQ (nonsymmetricF R t.1 t.2.1) ∧
    NonsymmetricPrefixDiagramMember R hB hQ (nonsymmetricX R t.1 t.2.2) ∧
    NonsymmetricPrefixDiagramMember R hB hQ (nonsymmetricY R t.2.1 t.2.2) ∧
    (t.1 < nsP R → t.2.1 < nsQ R →
      NonsymmetricPrefixDiagramMember R hB hQ (nonsymmetricO R t.2.2)) := by
  let t := nonsymmetricReturnTuple R hB ell
  have S := nonsymmetricReturnTuple_spec R hB ell
  have hp := nonsymmetric_coefficients R
  have dom := S.1
  unfold NonsymmetricLDomain at dom
  have bound {x y h : ℕ} (hc : NonsymmetricPrefixHeightCandidate R hB x y h) :=
    nonsymmetric_prefix_diagram_le_candidate R hB hQ hc
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨0,t.1,t.2.1,S.1,bound ⟨ell,Or.inl ⟨le_refl _,le_refl _,rfl⟩⟩,?_⟩
    simp only [t,nonsymmetricF,zero_mul,zero_add]
  · unfold nonsymmetricX
    split_ifs with hi
    · refine ⟨nsW R-t.2.2,t.1+nsZ R,0,⟨?_,?_,Or.inr hp.2.1⟩,?_,?_⟩
      · dsimp only [t]; omega
      · omega
      · exact bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,le_refl _,rfl⟩))))⟩
      · simp only [t,zero_mul,add_zero]
    · refine ⟨nsC1 R-t.2.2,t.1-nsP R,0,⟨?_,?_,Or.inr hp.2.1⟩,?_,?_⟩
      · dsimp only [t]; omega
      · omega
      · exact bound ⟨ell,Or.inr (Or.inr (Or.inl ⟨by omega,le_refl _,rfl⟩))⟩
      · simp only [t,zero_mul,add_zero]
  · unfold nonsymmetricY
    split_ifs with hj
    · refine ⟨nsU R-t.2.2,0,t.2.1+nsV R,⟨?_,?_,Or.inl hp.1⟩,?_,?_⟩
      · omega
      · dsimp only [t]; omega
      · exact bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hj,le_refl _,rfl⟩))))⟩
      · simp only [t,zero_mul,zero_add,add_zero]
    · refine ⟨nsC1 R-t.2.2,0,t.2.1-nsQ R,⟨?_,?_,Or.inl hp.1⟩,?_,?_⟩
      · omega
      · dsimp only [t]; omega
      · exact bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,le_refl _,rfl⟩)))⟩
      · simp only [t,zero_mul,zero_add,add_zero]
  · intro hi hj
    refine ⟨nsC1 R-t.2.2,0,0,⟨by omega,by omega,Or.inl hp.1⟩,
      bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩,?_⟩
    simp only [t,nonsymmetricO,zero_mul,add_zero]

theorem nonsymmetric_prefix_diagram_complete (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {h x y : ℕ}
    (hdom : NonsymmetricLDomain R x y)
    (hm : ((h*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ) ∈ nonsymmetricPrefixIdeal R hQ) :
    nonsymmetricPrefixDiagramHeight R hB hQ x y ≤ h := by
  let z := h*nsA R+x*nsB R+y*nsC R
  obtain ⟨ell,hc⟩ := (nonsymmetric_prefix_four_sources R hB hQ (z : ℤ)).mp hm
  have source := nonsymmetric_prefix_source_diagram_members R hB hQ ell
  have transport (g : ℕ) (hg : NonsymmetricPrefixDiagramMember R hB hQ g)
      (hc : (z : ℤ)-(g : ℤ) ∈ (nsH R).asRelativeIdeal) :
      NonsymmetricPrefixDiagramMember R hB hQ z := by
    obtain ⟨w,hw,he⟩ := hc
    have he' : z=g+w := by exact_mod_cast (show (z : ℤ)=(g : ℤ)+(w : ℤ) by omega)
    rw [he']; exact nonsymmetric_prefix_diagram_add_tail R hB hQ hg hw
  have hz : NonsymmetricPrefixDiagramMember R hB hQ z := by
    rcases hc with hf | hx | hy | ⟨hi,hj,ho⟩
    · exact transport _ source.1 hf
    · exact transport _ source.2.1 hx
    · exact transport _ source.2.2.1 hy
    · exact transport _ (source.2.2.2 hi hj) ho
  obtain ⟨h',x',y',hd',hh',he⟩ := hz
  have hi := nonsymmetric_lShape_degree_injective R hdom hd' he
  rcases hi with ⟨rfl,rfl,rfl⟩
  exact hh'

local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

theorem nonsymmetric_prefix_height_formula (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {x y : ℕ}
    (hdom : NonsymmetricLDomain R x y) :
    nonsymmetricPrefixLambda R hQ (gridResidue P.M.base (nsReindex R) x y)=
      (nonsymmetricPrefixDiagramHeight R hB hQ x y : ℤ)*nsA R+x*nsB R+y*nsC R := by
  let r := gridResidue P.M.base (nsReindex R) x y
  let lam := nonsymmetricPrefixLambda R hQ r
  have hm := (nonsymmetricPrefixIdeal R hQ).aperyRepresentative_mem (nsA R) r
  have hmod := (nonsymmetricPrefixIdeal R hQ).aperyRepresentative_mod (nsA R) r
  have ht : lam ∈ (nsH R).asRelativeIdeal := by
    obtain ⟨ell,hp,hl,he⟩ := hm
    exact he.1
  have hd : L5A2C4OR5.HerzogLShapeDomain (branchB_inactive_coherentHerzogData R) x y := by
    simpa only [NonsymmetricLDomain,L5A2C4OR5.HerzogLShapeDomain,
      branchB_inactive_coherent_c2,branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12,branchB_inactive_coherent_cr13] using hdom
  have hc := L5A2C4OR6.herzogLShapeCanonicality P.M.base (nsReindex R)
    (branchB_inactive_coherentHerzogData R) x y hd
  have halpha : physicalAlpha P.M.base (nsReindex R) r=(x : ℤ)*nsB R+y*nsC R := by
    rw [← hc]
    simp only [normalizedGrid,zero_mul,zero_add,Nat.cast_add,Nat.cast_mul]
  have hle := (nsH R).asRelativeIdeal.aperyRepresentative_le (nsA R) r ht hmod
  change physicalAlpha P.M.base (nsReindex R) r ≤ lam at hle
  rw [halpha] at hle
  have hmxy : (((x : ℤ)*nsB R+y*nsC R : ℤ) : ZMod (nsA R))=r := by
    simpa only [r,Int.cast_add,Int.cast_mul,Int.cast_natCast,normalizedGrid,zero_mul,zero_add,Nat.cast_add,Nat.cast_mul] using
      normalizedGrid_mod P.M.base (nsReindex R) 0 x y
  obtain ⟨h,he⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq (nsA R) hle (hmod.trans hmxy.symm)
  have hlgrid : ((h*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)=lam := by
    simp only [Nat.cast_add,Nat.cast_mul]; dsimp only [lam] at he; nlinarith only [he]
  have hlmem : ((h*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ) ∈ nonsymmetricPrefixIdeal R hQ := by
    rw [hlgrid]; exact hm
  have hl := nonsymmetric_prefix_diagram_complete R hB hQ hdom hlmem
  have hu := nonsymmetric_prefix_lambda_le_diagram R hB hQ x y
  have ha : (0 : ℤ) < nsA R := by exact_mod_cast routingA_pos P.M.base (nsReindex R)
  have hlZ : (nonsymmetricPrefixDiagramHeight R hB hQ x y : ℤ) ≤ h := by exact_mod_cast hl
  change lam=_
  change lam ≤ _ at hu
  nlinarith only [he,hlZ,ha,hu]

end NS25Lean.L5A2BFinalRepair
