import NS25Lean.P2BranchBPrefixCornerRouting

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}
local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

private theorem pred_mul {n g : ℕ} (hn : 0 < n) : (n-1)*g+g=n*g := by
  have he := congrArg (fun x => x*g) (Nat.sub_add_cancel (by omega : 1 ≤ n))
  simpa only [add_mul,one_mul] using he

theorem nonsymmetric_prefix_lowX_inverse_not_branch (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ell : NonsymmetricReturnIndex R)
    (hi : (nonsymmetricReturnTuple R hB ell).1 < nsP R) {r : ZMod (nsA R)}
    (ht : (nonsymmetricPrefixRouting R hQ).branchTarget r=
      gridResidue P.M.base (nsReindex R) ((nonsymmetricReturnTuple R hB ell).1+nsZ R) 0) :
    ¬ (nonsymmetricPrefixRouting R hQ).IsBranch r := by
  intro hr
  let i := (nonsymmetricReturnTuple R hB ell).1
  have S := nonsymmetricReturnTuple_spec R hB ell
  have hp := nonsymmetric_coefficients R
  have rel := (nonsymmetric_normalized_relations R).2.2
  have hcp : 0 < nsC3 R := by omega
  have pi := pred_mul (g:=nsB R) S.2.1
  have pc := pred_mul (g:=nsC R) hcp
  have d0 : NonsymmetricLDomain R (i-1) (nsC3 R-1) := ⟨by dsimp [i]; omega,by omega,Or.inl (by dsimp [i]; omega)⟩
  have dB : NonsymmetricLDomain R i (nsC3 R-1) := ⟨by dsimp [i]; omega,by omega,Or.inl hi⟩
  have dC : NonsymmetricLDomain R (i-1+nsZ R) 0 := ⟨by dsimp [i]; omega,by omega,Or.inr hp.2.1⟩
  have dT : NonsymmetricLDomain R (i+nsZ R) 0 := ⟨by dsimp [i]; omega,by omega,Or.inr hp.2.1⟩
  have B := nonsymmetric_prefix_b_edge R hB hQ d0 dB (carry:=0) (by
    dsimp [i]; simp only [zero_mul,zero_add]; omega)
  have BC := nonsymmetric_prefix_c_edge R hB hQ dB dT (carry:=nsW R) (by
    simp only [zero_mul,add_zero,add_mul]; omega)
  have C := nonsymmetric_prefix_c_edge R hB hQ d0 dC (carry:=nsW R) (by
    simp only [zero_mul,add_zero,add_mul]; omega)
  have inv : r=gridResidue P.M.base (nsReindex R) (i-1) (nsC3 R-1) := by
    apply (nonsymmetricPrefixRouting R hQ).b.injective
    apply (nonsymmetricPrefixRouting R hQ).c.injective
    change (nonsymmetricPrefixRouting R hQ).branchTarget r=_
    rw [ht,B.1,BC.1]
  rw [inv] at hr
  have hz : nonsymmetricPrefixDiagramHeight R hB hQ i (nsC3 R-1)=0 := by
    apply (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mpr
    have dom := S.1; unfold NonsymmetricLDomain at dom
    exact ⟨ell,le_refl _,by omega⟩
  have hb := B.2
  rw [hr.1,hz] at hb
  have baseZero : nonsymmetricPrefixDiagramHeight R hB hQ (i-1) (nsC3 R-1)=0 := by omega
  have hc := C.2
  rw [hr.2,baseZero] at hc
  obtain ⟨k,hki,hkj⟩ := (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mp baseZero
  have Ski := nonsymmetricReturnTuple_spec R hB k
  have hki' : (nonsymmetricReturnTuple R hB k).1 < nsP R := by dsimp [i] at hki; omega
  have bound := nonsymmetric_prefix_diagram_le_candidate R hB hQ
    (show NonsymmetricPrefixHeightCandidate R hB (i-1+nsZ R) 0
      (nsW R-(nonsymmetricReturnTuple R hB k).2.2) from
      ⟨k,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hki',by omega,rfl⟩))))⟩)
  have depth := Ski.2.2.2.1
  have depthBound := Ski.2.2.2.2.1 hki'
  omega

theorem nonsymmetric_prefix_lowY_inverse_not_branch (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ell : NonsymmetricReturnIndex R)
    (hj : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) {r : ZMod (nsA R)}
    (ht : (nonsymmetricPrefixRouting R hQ).branchTarget r=
      gridResidue P.M.base (nsReindex R) 0 ((nonsymmetricReturnTuple R hB ell).2.1+nsV R)) :
    ¬ (nonsymmetricPrefixRouting R hQ).IsBranch r := by
  intro hr
  let j := (nonsymmetricReturnTuple R hB ell).2.1
  have S := nonsymmetricReturnTuple_spec R hB ell
  have hp := nonsymmetric_coefficients R
  have rel := (nonsymmetric_normalized_relations R).2.1
  have hbp : 0 < nsC2 R := by omega
  have pj := pred_mul (g:=nsC R) S.2.2.1
  have pb := pred_mul (g:=nsB R) hbp
  have d0 : NonsymmetricLDomain R (nsC2 R-1) (j-1) := ⟨by omega,by dsimp [j]; omega,Or.inr (by dsimp [j]; omega)⟩
  have dC : NonsymmetricLDomain R (nsC2 R-1) j := ⟨by omega,by dsimp [j]; omega,Or.inr hj⟩
  have dB : NonsymmetricLDomain R 0 (j-1+nsV R) := ⟨by omega,by dsimp [j]; omega,Or.inl hp.1⟩
  have dT : NonsymmetricLDomain R 0 (j+nsV R) := ⟨by omega,by dsimp [j]; omega,Or.inl hp.1⟩
  have C := nonsymmetric_prefix_c_edge R hB hQ d0 dC (carry:=0) (by
    dsimp [j]; simp only [zero_mul,zero_add]; omega)
  have CB := nonsymmetric_prefix_b_edge R hB hQ dC dT (carry:=nsU R) (by
    simp only [zero_mul,add_zero,zero_add,add_mul]; omega)
  have B := nonsymmetric_prefix_b_edge R hB hQ d0 dB (carry:=nsU R) (by
    simp only [zero_mul,add_zero,zero_add,add_mul]; omega)
  have inv : r=gridResidue P.M.base (nsReindex R) (nsC2 R-1) (j-1) := by
    apply (nonsymmetricPrefixRouting R hQ).c.injective
    apply (nonsymmetricPrefixRouting R hQ).b.injective
    have commute := (nonsymmetricPrefixRouting R hQ).commute r
    change (nonsymmetricPrefixRouting R hQ).b ((nonsymmetricPrefixRouting R hQ).c r)=_
    rw [commute,C.1,CB.1]
    exact ht
  rw [inv] at hr
  have hz : nonsymmetricPrefixDiagramHeight R hB hQ (nsC2 R-1) j=0 := by
    apply (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mpr
    have dom := S.1; unfold NonsymmetricLDomain at dom
    exact ⟨ell,by omega,le_refl _⟩
  have hc := C.2
  rw [hr.2,hz] at hc
  have baseZero : nonsymmetricPrefixDiagramHeight R hB hQ (nsC2 R-1) (j-1)=0 := by omega
  have hb := B.2
  rw [hr.1,baseZero] at hb
  obtain ⟨k,hki,hkj⟩ := (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mp baseZero
  have Skj := nonsymmetricReturnTuple_spec R hB k
  have hkj' : (nonsymmetricReturnTuple R hB k).2.1 < nsQ R := by dsimp [j] at hkj; omega
  have bound := nonsymmetric_prefix_diagram_le_candidate R hB hQ
    (show NonsymmetricPrefixHeightCandidate R hB 0 (j-1+nsV R)
      (nsU R-(nonsymmetricReturnTuple R hB k).2.2) from
      ⟨k,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hkj',by omega,rfl⟩))))⟩)
  have depth := Skj.2.2.2.1
  have depthBound := Skj.2.2.2.2.2.1 hkj'
  omega

theorem nonsymmetric_prefix_highX_inverse_not_branch (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ell : NonsymmetricReturnIndex R)
    (hi : nsP R < (nonsymmetricReturnTuple R hB ell).1) {r : ZMod (nsA R)}
    (ht : (nonsymmetricPrefixRouting R hQ).branchTarget r=
      gridResidue P.M.base (nsReindex R) ((nonsymmetricReturnTuple R hB ell).1-nsP R) 0) :
    ¬ (nonsymmetricPrefixRouting R hQ).IsBranch r := by
  intro hr
  let i := (nonsymmetricReturnTuple R hB ell).1
  have S := nonsymmetricReturnTuple_spec R hB ell
  have dom := S.1; unfold NonsymmetricLDomain at dom
  have hp := nonsymmetric_coefficients R
  have rel := (nonsymmetric_normalized_relations R).1
  have pi := pred_mul (g:=nsB R) S.2.1
  have pq := pred_mul (g:=nsC R) hp.2.1
  have psub := congrArg (fun n => n*nsB R) (Nat.sub_add_cancel (by dsimp [i]; omega : nsP R ≤ i))
  simp only [add_mul] at psub
  have d0 : NonsymmetricLDomain R (i-1) (nsQ R-1) := ⟨by dsimp [i]; omega,by omega,Or.inr (by omega)⟩
  have dB : NonsymmetricLDomain R i (nsQ R-1) := ⟨dom.1,by omega,Or.inr (by omega)⟩
  have dT : NonsymmetricLDomain R (i-nsP R) 0 := ⟨by dsimp [i]; omega,by omega,Or.inr hp.2.1⟩
  have B := nonsymmetric_prefix_b_edge R hB hQ d0 dB (carry:=0) (by
    dsimp [i]; simp only [zero_mul,zero_add]; omega)
  have BC := nonsymmetric_prefix_c_edge R hB hQ dB dT (carry:=nsC1 R) (by
    dsimp [i] at psub ⊢; simp only [zero_mul,add_zero]; omega)
  have inv : r=gridResidue P.M.base (nsReindex R) (i-1) (nsQ R-1) := by
    apply (nonsymmetricPrefixRouting R hQ).b.injective
    apply (nonsymmetricPrefixRouting R hQ).c.injective
    change (nonsymmetricPrefixRouting R hQ).branchTarget r=_
    rw [ht,B.1,BC.1]
  rw [inv] at hr
  have psub' := congrArg (fun n => n*nsB R) (Nat.sub_add_cancel (by dsimp [i]; omega : nsP R ≤ i-1))
  simp only [add_mul] at psub'
  have dC : NonsymmetricLDomain R (i-1-nsP R) 0 := ⟨by dsimp [i]; omega,by omega,Or.inr hp.2.1⟩
  have C := nonsymmetric_prefix_c_edge R hB hQ d0 dC (carry:=nsC1 R) (by
    dsimp [i] at psub' ⊢; simp only [zero_mul,add_zero]; omega)
  have hlt := nonsymmetric_prefix_diagram_height_lt_c1 R hB hQ (i-1-nsP R) 0
  have hc := C.2
  rw [hr.2] at hc
  omega

theorem nonsymmetric_prefix_highY_inverse_not_branch (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ell : NonsymmetricReturnIndex R)
    (hj : nsQ R < (nonsymmetricReturnTuple R hB ell).2.1) {r : ZMod (nsA R)}
    (ht : (nonsymmetricPrefixRouting R hQ).branchTarget r=
      gridResidue P.M.base (nsReindex R) 0 ((nonsymmetricReturnTuple R hB ell).2.1-nsQ R)) :
    ¬ (nonsymmetricPrefixRouting R hQ).IsBranch r := by
  intro hr
  let j := (nonsymmetricReturnTuple R hB ell).2.1
  have S := nonsymmetricReturnTuple_spec R hB ell
  have dom := S.1; unfold NonsymmetricLDomain at dom
  have hp := nonsymmetric_coefficients R
  have rel := (nonsymmetric_normalized_relations R).1
  have pj := pred_mul (g:=nsC R) S.2.2.1
  have pp := pred_mul (g:=nsB R) hp.1
  have qsub := congrArg (fun n => n*nsC R) (Nat.sub_add_cancel (by dsimp [j]; omega : nsQ R ≤ j))
  simp only [add_mul] at qsub
  have d0 : NonsymmetricLDomain R (nsP R-1) (j-1) := ⟨by omega,by dsimp [j]; omega,Or.inl (by omega)⟩
  have dC : NonsymmetricLDomain R (nsP R-1) j := ⟨by omega,dom.2.1,Or.inl (by omega)⟩
  have dT : NonsymmetricLDomain R 0 (j-nsQ R) := ⟨by omega,by dsimp [j]; omega,Or.inl hp.1⟩
  have C := nonsymmetric_prefix_c_edge R hB hQ d0 dC (carry:=0) (by
    dsimp [j]; simp only [zero_mul,zero_add]; omega)
  have CB := nonsymmetric_prefix_b_edge R hB hQ dC dT (carry:=nsC1 R) (by
    dsimp [j] at qsub ⊢; simp only [zero_mul,add_zero,zero_add]; omega)
  have inv : r=gridResidue P.M.base (nsReindex R) (nsP R-1) (j-1) := by
    apply (nonsymmetricPrefixRouting R hQ).c.injective
    apply (nonsymmetricPrefixRouting R hQ).b.injective
    have commute := (nonsymmetricPrefixRouting R hQ).commute r
    change (nonsymmetricPrefixRouting R hQ).b ((nonsymmetricPrefixRouting R hQ).c r)=_
    rw [commute,C.1,CB.1]; exact ht
  rw [inv] at hr
  have qsub' := congrArg (fun n => n*nsC R) (Nat.sub_add_cancel (by dsimp [j]; omega : nsQ R ≤ j-1))
  simp only [add_mul] at qsub'
  have dB : NonsymmetricLDomain R 0 (j-1-nsQ R) := ⟨by omega,by dsimp [j]; omega,Or.inl hp.1⟩
  have B := nonsymmetric_prefix_b_edge R hB hQ d0 dB (carry:=nsC1 R) (by
    dsimp [j] at qsub' ⊢; simp only [zero_mul,add_zero,zero_add]; omega)
  have hlt := nonsymmetric_prefix_diagram_height_lt_c1 R hB hQ 0 (j-1-nsQ R)
  have hb := B.2
  rw [hr.1] at hb
  omega

theorem nonsymmetric_prefix_origin_inverse_center (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {r : ZMod (nsA R)}
    (hr : (nonsymmetricPrefixRouting R hQ).IsBranch r)
    (ht : (nonsymmetricPrefixRouting R hQ).branchTarget r=gridResidue P.M.base (nsReindex R) 0 0) :
    ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := by
  have hp := nonsymmetric_coefficients R
  have rel := (nonsymmetric_normalized_relations R).1
  have pp := pred_mul (g:=nsB R) hp.1
  have pq := pred_mul (g:=nsC R) hp.2.1
  have d0 : NonsymmetricLDomain R (nsP R-1) (nsQ R-1) := ⟨by omega,by omega,Or.inl (by omega)⟩
  have dB : NonsymmetricLDomain R (nsP R) (nsQ R-1) := ⟨by omega,by omega,Or.inr (by omega)⟩
  have dC : NonsymmetricLDomain R (nsP R-1) (nsQ R) := ⟨by omega,by omega,Or.inl (by omega)⟩
  have dT : NonsymmetricLDomain R 0 0 := ⟨by omega,by omega,Or.inl hp.1⟩
  have B := nonsymmetric_prefix_b_edge R hB hQ d0 dB (carry:=0) (by
    simp only [zero_mul,zero_add]; omega)
  have C := nonsymmetric_prefix_c_edge R hB hQ d0 dC (carry:=0) (by
    simp only [zero_mul,zero_add]; omega)
  have BC := nonsymmetric_prefix_c_edge R hB hQ dB dT (carry:=nsC1 R) (by
    simp only [zero_mul,add_zero]; omega)
  have inv : r=gridResidue P.M.base (nsReindex R) (nsP R-1) (nsQ R-1) := by
    apply (nonsymmetricPrefixRouting R hQ).b.injective
    apply (nonsymmetricPrefixRouting R hQ).c.injective
    change (nonsymmetricPrefixRouting R hQ).branchTarget r=_
    rw [ht,B.1,BC.1]
  rw [inv] at hr
  obtain ⟨ell,hi,hj⟩ := nonsymmetric_inclusive_origin_return R hB hQ
  by_cases hip : (nonsymmetricReturnTuple R hB ell).1 < nsP R
  · by_cases hjq : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R
    · exact ⟨ell,hip,hjq⟩
    · have h0 : nonsymmetricPrefixDiagramHeight R hB hQ (nsP R-1) (nsQ R)=0 := by
        apply (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mpr
        exact ⟨ell,by omega,hj⟩
      have hc := C.2
      rw [hr.2,h0] at hc
      obtain ⟨k,hki,hkj⟩ := (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mp (by omega :
        nonsymmetricPrefixDiagramHeight R hB hQ (nsP R-1) (nsQ R-1)=0)
      exact ⟨k,by omega,by omega⟩
  · have S := nonsymmetricReturnTuple_spec R hB ell
    have hjq : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := by
      rcases S.1.2.2 with h | h <;> omega
    have h0 : nonsymmetricPrefixDiagramHeight R hB hQ (nsP R) (nsQ R-1)=0 := by
      apply (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mpr
      exact ⟨ell,hi,by omega⟩
    have hb := B.2
    rw [hr.1,h0] at hb
    obtain ⟨k,hki,hkj⟩ := (nonsymmetric_prefix_diagram_height_zero_iff R hB hQ _ _).mp (by omega :
      nonsymmetricPrefixDiagramHeight R hB hQ (nsP R-1) (nsQ R-1)=0)
    exact ⟨k,by omega,by omega⟩

theorem nonsymmetric_prefix_C_targets_F_or_origin (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) {r : ZMod (nsA R)}
    (hr : (nonsymmetricPrefixRouting R hQ).IsBranch r)
    (hs : (nonsymmetricPrefixRouting R hQ).IsSource ((nonsymmetricPrefixRouting R hQ).branchTarget r)) :
    (∃ ell : NonsymmetricReturnIndex R,
      nonsymmetricPrefixLambda R hQ ((nonsymmetricPrefixRouting R hQ).branchTarget r)=
        (nonsymmetricF R (nonsymmetricReturnTuple R hB ell).1
          (nonsymmetricReturnTuple R hB ell).2.1 : ℕ)) ∨
    ((nonsymmetricPrefixRouting R hQ).branchTarget r=gridResidue P.M.base (nsReindex R) 0 0 ∧
      ∃ ell : NonsymmetricReturnIndex R,
        (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
        (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) := by
  let t := (nonsymmetricPrefixRouting R hQ).branchTarget r
  let z := nonsymmetricPrefixLambda R hQ t
  have hgen := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base (nsReindex R))).1
  have pos := nonsymmetric_generators_positive R
  have hmin : (nonsymmetricPrefixIdeal R hQ).IsMinimalGenerator z :=
    ((nonsymmetricPrefixIdeal R hQ).concrete_isSource_iff_isMinimalGenerator
      (nsA R) (nsB R) (nsC R) hgen (routingHB _ _) (routingHC _ _) pos.2.1.ne' pos.2.2.ne' t).mp hs
  obtain ⟨ell,hc⟩ := nonsymmetric_prefix_minimal_source_value R hB hQ hmin
  have hmod := (nonsymmetricPrefixIdeal R hQ).aperyRepresentative_mod (nsA R) t
  change (z : ZMod (nsA R))=t at hmod
  have grid {height x y : ℕ} (he : z=((height*nsA R+x*nsB R+y*nsC R : ℕ) : ℤ)) :
      t=gridResidue P.M.base (nsReindex R) x y := by
    have hm := normalizedGrid_mod P.M.base (nsReindex R) height x y
    rw [he] at hmod
    exact hmod.symm.trans (by simpa only [normalizedGrid,Int.cast_natCast] using hm)
  rcases hc with hf | hx | hy | ⟨hi,hj,ho⟩
  · exact Or.inl ⟨ell,hf⟩
  · by_cases hi : (nonsymmetricReturnTuple R hB ell).1 < nsP R
    · have he : z=(((nsW R-(nonsymmetricReturnTuple R hB ell).2.2)*nsA R+
        ((nonsymmetricReturnTuple R hB ell).1+nsZ R)*nsB R+0*nsC R : ℕ) : ℤ) := by
        simpa only [nonsymmetricX,ite_eq_left hi,zero_mul,add_zero] using hx
      exact (nonsymmetric_prefix_lowX_inverse_not_branch R hB hQ ell hi (grid he) hr).elim
    · have he : z=(((nsC1 R-(nonsymmetricReturnTuple R hB ell).2.2)*nsA R+
        ((nonsymmetricReturnTuple R hB ell).1-nsP R)*nsB R+0*nsC R : ℕ) : ℤ) := by
        simpa only [nonsymmetricX,ite_eq_right hi,zero_mul,add_zero] using hx
      have ht := grid he
      by_cases heq : (nonsymmetricReturnTuple R hB ell).1=nsP R
      · simp only [heq,Nat.sub_self] at ht
        exact Or.inr ⟨ht,nonsymmetric_prefix_origin_inverse_center R hB hQ hr ht⟩
      · exact (nonsymmetric_prefix_highX_inverse_not_branch R hB hQ ell (by omega) ht hr).elim
  · by_cases hj : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R
    · have he : z=(((nsU R-(nonsymmetricReturnTuple R hB ell).2.2)*nsA R+
        0*nsB R+((nonsymmetricReturnTuple R hB ell).2.1+nsV R)*nsC R : ℕ) : ℤ) := by
        simpa only [nonsymmetricY,ite_eq_left hj,zero_mul,add_zero] using hy
      exact (nonsymmetric_prefix_lowY_inverse_not_branch R hB hQ ell hj (grid he) hr).elim
    · have he : z=(((nsC1 R-(nonsymmetricReturnTuple R hB ell).2.2)*nsA R+
        0*nsB R+((nonsymmetricReturnTuple R hB ell).2.1-nsQ R)*nsC R : ℕ) : ℤ) := by
        simpa only [nonsymmetricY,ite_eq_right hj,zero_mul,add_zero] using hy
      have ht := grid he
      by_cases heq : (nonsymmetricReturnTuple R hB ell).2.1=nsQ R
      · simp only [heq,Nat.sub_self] at ht
        exact Or.inr ⟨ht,nonsymmetric_prefix_origin_inverse_center R hB hQ hr ht⟩
      · exact (nonsymmetric_prefix_highY_inverse_not_branch R hB hQ ell (by omega) ht hr).elim
  · have he : z=(((nsC1 R-(nonsymmetricReturnTuple R hB ell).2.2)*nsA R+0*nsB R+0*nsC R : ℕ) : ℤ) := by
      simpa only [nonsymmetricO,zero_mul,add_zero] using ho
    have ht := grid he
    exact Or.inr ⟨ht,nonsymmetric_prefix_origin_inverse_center R hB hQ hr ht⟩

end NS25Lean.L5A2BFinalRepair
