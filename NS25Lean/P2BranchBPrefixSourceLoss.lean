import NS25Lean.P2BranchBBalancedPrefixSlack

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}
local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

abbrev NonsymmetricPrefixSources (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  {s : ℤ // (nonsymmetricPrefixIdeal R hQ).IsMinimalGenerator s}
def NonsymmetricErasedSources (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  {s : NonsymmetricPrefixSources R hQ //
    s.val-(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) ∈ (nsH R).asRelativeIdeal}

private theorem nat_mem {H : NumericalSemigroup} {n : ℕ}
    (h : (n : ℤ) ∈ H.asRelativeIdeal) : n ∈ H := by
  obtain ⟨t,ht,he⟩ := h
  have hn : n=t := by exact_mod_cast he
  exact hn ▸ ht

private theorem pure_axis_not_return (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    {ell t : ℕ} (hp : 0 < ell) :
    (t < nsC2 R → ((t*nsB R : ℕ) : ℤ) ∉ returnIdeal (nsH R) (ell*normalizedM P.M.base)) ∧
    (t < nsC3 R → ((t*nsC R : ℕ) : ℤ) ∉ returnIdeal (nsH R) (ell*normalizedM P.M.base)) := by
  have live := nonsymmetric_live_pure_predecessors R hB
  constructor
  · intro ht hm
    have hadd := (routingI P.M.base (nsReindex R)).add_mem
      (nonsymmetric_returnIdeal_le_final R hp hm)
      (nat_mem (by simpa only [zero_mul,zero_add,add_zero] using nonsymmetric_grid_mem R 0 (nsC2 R-1-t) 0))
    apply live.1
    have hs : t+(nsC2 R-1-t)=nsC2 R-1 := by omega
    have he : (((nsC2 R-1)*nsB R : ℕ) : ℤ)=(t*nsB R : ℕ)+((nsC2 R-1-t)*nsB R : ℕ) := by
      exact_mod_cast (show (nsC2 R-1)*nsB R=t*nsB R+(nsC2 R-1-t)*nsB R by rw [← add_mul,hs])
    rw [he]
    exact hadd
  · intro ht hm
    have hadd := (routingI P.M.base (nsReindex R)).add_mem
      (nonsymmetric_returnIdeal_le_final R hp hm)
      (nat_mem (by simpa only [zero_mul,zero_add] using nonsymmetric_grid_mem R 0 0 (nsC3 R-1-t)))
    apply live.2
    have hs : t+(nsC3 R-1-t)=nsC3 R-1 := by omega
    have he : (((nsC3 R-1)*nsC R : ℕ) : ℤ)=(t*nsC R : ℕ)+((nsC3 R-1-t)*nsC R : ℕ) := by
      exact_mod_cast (show (nsC3 R-1)*nsC R=t*nsC R+(nsC3 R-1-t)*nsC R by rw [← add_mul,hs])
    rw [he]
    exact hadd

private theorem pure_a_not_return (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    {ell t : ℕ} (hp : 0 < ell) (ht : t < nsU R ∨ t < nsW R) :
    ((t*nsA R : ℕ) : ℤ) ∉ returnIdeal (nsH R) (ell*normalizedM P.M.base) := by
  intro hm
  have hI := nonsymmetric_returnIdeal_le_final R hp hm
  have live := branchB_inactive_active_gate_liveness R hB
  rcases ht with ht | ht
  · have hadd := (routingI P.M.base (nsReindex R)).add_mem hI
      (nat_mem (by simpa only [zero_mul,zero_add] using nonsymmetric_grid_mem R (nsU R-1-t) 0 (nsV R)))
    have he : ((t*nsA R : ℕ) : ℤ)+(( (nsU R-1-t)*nsA R+nsV R*nsC R : ℕ) : ℤ)=
        ((normalizedGrid P.M.base (nsReindex R) (nsU R-1) 0 (nsV R) : ℕ) : ℤ) := by
      have hs : t+(nsU R-1-t)=nsU R-1 := by omega
      simp only [normalizedGrid,zero_mul,zero_add,Nat.cast_add,Nat.cast_mul]
      exact_mod_cast (show t*nsA R+((nsU R-1-t)*nsA R+nsV R*nsC R)=
        (nsU R-1)*nsA R+nsV R*nsC R by calc
          _ = (t+(nsU R-1-t))*nsA R+nsV R*nsC R := by ring
          _ = _ := by rw [hs])
    have hg := (normalizedGrid_mem_iff_eta_le P.M.base (nsReindex R) (nsU R-1) 0 (nsV R)).mp (he ▸ hadd)
    have hl : nsU R ≤ eta P.M.base (nsReindex R) 0 (nsV R) := live.2.1
    omega
  · have hadd := (routingI P.M.base (nsReindex R)).add_mem hI
      (nat_mem (by simpa only [zero_mul,add_zero] using nonsymmetric_grid_mem R (nsW R-1-t) (nsZ R) 0))
    have he : ((t*nsA R : ℕ) : ℤ)+(((nsW R-1-t)*nsA R+nsZ R*nsB R : ℕ) : ℤ)=
        ((normalizedGrid P.M.base (nsReindex R) (nsW R-1) (nsZ R) 0 : ℕ) : ℤ) := by
      have hs : t+(nsW R-1-t)=nsW R-1 := by omega
      simp only [normalizedGrid,zero_mul,add_zero,Nat.cast_add,Nat.cast_mul]
      exact_mod_cast (show t*nsA R+((nsW R-1-t)*nsA R+nsZ R*nsB R)=
        (nsW R-1)*nsA R+nsZ R*nsB R by calc
          _ = (t+(nsW R-1-t))*nsA R+nsZ R*nsB R := by ring
          _ = _ := by rw [hs])
    have hg := (normalizedGrid_mem_iff_eta_le P.M.base (nsReindex R) (nsW R-1) (nsZ R) 0).mp (he ▸ hadd)
    have hl : nsW R ≤ eta P.M.base (nsReindex R) (nsZ R) 0 := live.2.2
    omega

private theorem minimal_eq {H : NumericalSemigroup} (I : RelativeIdeal H) {s t : ℤ}
    (hs : I.IsMinimalGenerator s) (ht : t ∈ I) (hd : s-t ∈ H.asRelativeIdeal) : s=t := by
  obtain ⟨n,hn,he⟩ := hd
  by_cases h0 : n=0
  · simp only [h0,Nat.cast_zero] at he; omega
  · exact (hs.2 n hn h0 (by convert ht using 1; omega)).elim

theorem nonsymmetric_erased_source_is_CENTER_O (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (s : NonsymmetricErasedSources R hQ) :
    ∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R ∧
      s.val.val=(nonsymmetricO R (nonsymmetricReturnTuple R hB ell).2.2 : ℕ) := by
  obtain ⟨l,hp,hl,hmem⟩ := s.val.property.1
  let ell : NonsymmetricReturnIndex R := ⟨l,hp,hl⟩
  have S := nonsymmetricReturnTuple_spec R hB ell
  have eqn := S.2.2.2.2.2.2
  have gen := (nonsymmetric_single_return_four_sources R hB hp S.1 eqn s.val.val).mp hmem
  have mem := nonsymmetric_single_return_sources_mem R hB hp S.1 eqn
  have dif := nonsymmetric_single_return_source_differences R hB hp S.1 eqn
  have compl {g : ℕ} (hg : (g : ℤ) ∈ returnIdeal (nsH R) (l*normalizedM P.M.base))
      (hs : s.val.val=g) :
      s.val.val-(l*normalizedM P.M.base : ℕ) ∈
        returnIdeal (nsH R) ((actualPrincipalIndex P.M.base-l)*normalizedM P.M.base) := by
    refine ⟨hs ▸ hg.2,?_⟩
    change _- _ ∈ (nsH R).asRelativeIdeal
    have he : ((actualPrincipalIndex P.M.base-l)*normalizedM P.M.base : ℕ)+(l*normalizedM P.M.base : ℤ)=
        (actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) := by
      exact_mod_cast (show (actualPrincipalIndex P.M.base-l)*normalizedM P.M.base+l*normalizedM P.M.base=
        actualPrincipalIndex P.M.base*normalizedM P.M.base by rw [← add_mul,Nat.sub_add_cancel (by omega)])
    have same : s.val.val-(l*normalizedM P.M.base : ℕ)-
        ((actualPrincipalIndex P.M.base-l)*normalizedM P.M.base : ℕ)=
        s.val.val-(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) := by omega
    exact same.symm ▸ s.property
  have hcpos : 0 < actualPrincipalIndex P.M.base-l := by omega
  rcases gen with hf | hx | hy | ⟨hi,hj,ho⟩
  · have he := minimal_eq _ s.val.property ⟨l,hp,hl,mem.1⟩ hf
    have hcompl := compl mem.1 he
    rw [he,dif.1] at hcompl
    have hd : (nonsymmetricReturnTuple R hB ell).2.2 < nsU R ∨
        (nonsymmetricReturnTuple R hB ell).2.2 < nsW R := by
      rcases S.1.2.2 with hi | hj
      · exact Or.inr (S.2.2.2.2.1 hi)
      · exact Or.inl (S.2.2.2.2.2.1 hj)
    exact (pure_a_not_return R hB hcpos hd hcompl).elim
  · have he := minimal_eq _ s.val.property ⟨l,hp,hl,mem.2.1⟩ hx
    have hcompl := compl mem.2.1 he
    rw [he,dif.2.1] at hcompl
    have hlt : (if (nonsymmetricReturnTuple R hB ell).1 < nsP R then
        nsC3 R-(nonsymmetricReturnTuple R hB ell).2.1 else
        nsQ R-(nonsymmetricReturnTuple R hB ell).2.1) < nsC3 R := by
      have cc := nonsymmetric_coefficients R
      split_ifs <;> omega
    exact ((pure_axis_not_return R hB hcpos).2 hlt hcompl).elim
  · have he := minimal_eq _ s.val.property ⟨l,hp,hl,mem.2.2.1⟩ hy
    have hcompl := compl mem.2.2.1 he
    rw [he,dif.2.2.1] at hcompl
    have hlt : (if (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R then
        nsC2 R-(nonsymmetricReturnTuple R hB ell).1 else
        nsP R-(nonsymmetricReturnTuple R hB ell).1) < nsC2 R := by
      have cc := nonsymmetric_coefficients R
      split_ifs <;> omega
    exact ((pure_axis_not_return R hB hcpos).1 hlt hcompl).elim
  · exact ⟨ell,hi,hj,minimal_eq _ s.val.property ⟨l,hp,hl,mem.2.2.2 hi hj⟩ ho⟩

theorem nonsymmetric_erased_sources_subsingleton (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Subsingleton (NonsymmetricErasedSources R hQ) := by
  refine ⟨fun s t => ?_⟩
  obtain ⟨ls,_,_,hs⟩ := nonsymmetric_erased_source_is_CENTER_O R hB hQ s
  obtain ⟨lt,_,_,ht⟩ := nonsymmetric_erased_source_is_CENTER_O R hB hQ t
  let a := nsC1 R-(nonsymmetricReturnTuple R hB ls).2.2
  let b := nsC1 R-(nonsymmetricReturnTuple R hB lt).2.2
  have eqst : s.val.val=t.val.val := by
    rcases le_total a b with h | h
    · apply (minimal_eq _ t.val.property s.val.property.1 ?_).symm
      rw [hs,ht]
      have hm := nonsymmetric_grid_mem R (b-a) 0 0
      convert hm using 1
      simp only [nonsymmetricO,Nat.cast_mul,Nat.cast_sub h,zero_mul,add_zero]
      change (b : ℤ)*nsA R-a*nsA R=((b : ℤ)-a)*nsA R
      ring
    · apply minimal_eq _ s.val.property t.val.property.1
      rw [hs,ht]
      have hm := nonsymmetric_grid_mem R (a-b) 0 0
      convert hm using 1
      simp only [nonsymmetricO,Nat.cast_mul,Nat.cast_sub h,zero_mul,add_zero]
      change (a : ℤ)*nsA R-b*nsA R=((a : ℤ)-b)*nsA R
      ring
  exact Subtype.ext (Subtype.ext eqst)

def nonsymmetricSourceLoss (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) : ℕ := Nat.card (NonsymmetricErasedSources R hQ)

theorem nonsymmetric_source_loss_zero_or_one (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricSourceLoss R hQ=0 ∨ nonsymmetricSourceLoss R hQ=1 := by
  letI := nonsymmetric_erased_sources_subsingleton R hB hQ
  have hi : Function.Injective (fun _ : NonsymmetricErasedSources R hQ => ()) :=
    fun _ _ _ => Subsingleton.elim _ _
  have hh : Nat.card (NonsymmetricErasedSources R hQ) ≤ 1 := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_unit] using Nat.card_le_card_of_injective _ hi
  unfold nonsymmetricSourceLoss
  omega

abbrev NonsymmetricSurvivingSources (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  {s : NonsymmetricPrefixSources R hQ //
    s.val-(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) ∉ (nsH R).asRelativeIdeal}
abbrev NonsymmetricFinalSources (R : SectorBCriticalRoleBranchB P) :=
  {s : ℤ // IsSource (nsH R) (finalCarrier (nsH R) (normalizedM P.M.base)
    (actualPrincipalIndex P.M.base)) s}

theorem nonsymmetric_surviving_source_is_final (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (s : NonsymmetricSurvivingSources R hQ) :
    IsSource (nsH R) (finalCarrier (nsH R) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)) s.val.val := by
  refine ⟨Or.inl s.val.property.1,?_⟩
  intro t ht ht0 hm
  rcases hm with hm | hm
  · exact s.val.property.2 t ht ht0 hm
  · apply s.property
    have hh := (nsH R).asRelativeIdeal.add_mem hm ht
    change s.val.val-(t : ℤ)-(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)+(t : ℤ) ∈
      (nsH R).asRelativeIdeal at hh
    convert hh using 1 <;> ring

def nonsymmetricSourceInsertionEquiv (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    NonsymmetricFinalSources R ≃ NonsymmetricSurvivingSources R hQ ⊕ Unit where
  toFun s := if he : s.val=(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)
    then Sum.inr () else Sum.inl ⟨⟨s.val,branchBirth_isPrefixSource ⟨s.property,he⟩⟩,by
      intro hm
      obtain ⟨t,ht,hte⟩ := hm
      change s.val-(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)=(t : ℤ) at hte
      have ht0 : t ≠ 0 := by intro h0; simp only [h0,Nat.cast_zero] at hte; omega
      apply s.property.2 t ht ht0
      apply Or.inr
      have eq : s.val-(t : ℤ)=(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) := by omega
      rw [eq]
      exact ⟨0,(nsH R).zero_mem,by simp⟩⟩
  invFun s := match s with
    | Sum.inl s => ⟨s.val.val,nonsymmetric_surviving_source_is_final R hQ s⟩
    | Sum.inr _ => ⟨(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ),by
        have hp := principal_is_new_source (normalizedH P.M.base)
          (normalizedM P.M.base) P.M.base.q_positive
        simpa only [nsH,nsReindex,branchBRoutingH_eq_normalizedH R] using hp⟩
  left_inv := by
    intro s
    dsimp only
    by_cases he : s.val=(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)
    · simp only [dif_pos he]
      exact Subtype.ext he.symm
    · simp only [dif_neg he]
  right_inv := by
    intro s
    cases s with
    | inl s =>
      have hn : s.val.val ≠ (actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) := by
        intro he
        apply s.property
        rw [he]
        exact ⟨0,(nsH R).zero_mem,by ring⟩
      simp only [dif_neg hn]
    | inr s => cases s; simp

theorem nonsymmetric_prefix_sources_finite (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Finite (NonsymmetricPrefixSources R hQ) := by
  let f : NonsymmetricPrefixSources R hQ → ZMod (nsA R) := fun s => (s.val : ZMod (nsA R))
  apply Finite.of_injective f
  intro s t he
  apply Subtype.ext
  have hgen := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base (nsReindex R))).1
  have hs := (nonsymmetricPrefixIdeal R hQ).aperyRepresentative_eq_of_isMinimalGenerator
    (nsA R) (nsB R) (nsC R) hgen s.property
  have ht := (nonsymmetricPrefixIdeal R hQ).aperyRepresentative_eq_of_isMinimalGenerator
    (nsA R) (nsB R) (nsC R) hgen t.property
  change (s.val : ZMod (nsA R))=(t.val : ZMod (nsA R)) at he
  rw [he] at hs
  exact hs.symm.trans ht

theorem nonsymmetric_final_source_count_dictionary (R : SectorBCriticalRoleBranchB P) :
    Nat.card (NonsymmetricFinalSources R)=P.sourceCount := by
  have he : Nat.card (NonsymmetricFinalSources R)=(normalizedI P.M.base).generatorCount := by
    simp only [NonsymmetricFinalSources,nsH,nsReindex,branchBRoutingH_eq_normalizedH R]
    change Nat.card {s : ℤ // IsSource (normalizedH P.M.base)
      (actualFinalCarrier P.M.base) s} = (normalizedI P.M.base).generatorCount
    rw [← normalizedTailIdeal_eq_actualFinalCarrier P.M.base]
    rfl
  rw [he]
  calc
    _ = tailGeneratorCount
        (generatedThree (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val)
        (aperyTail Gamma.toAddSubmonoid
          (generatedThree (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val)
          P.M.base.q.val) := normalizedTail_generatorCount Gamma _ _ _ _ (L5A2B2.chosenBase_minimalFour P.M.base)
    _ = P.sourceCount := by
      rw [P2Data.sourceCount,L2B.sourceCount,Data.K]
      exact (congrArg (fun H => tailGeneratorCount H
        (aperyTail Gamma.toAddSubmonoid H P.M.base.q.val))
        (L5A2B2.chosenBase_tail_eq_generatedThree P.M.base)).symm

theorem nonsymmetric_DeltaSource_eq_one_sub_loss (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricDeltaSource R hQ=1-(nonsymmetricSourceLoss R hQ : ℤ) := by
  letI := nonsymmetric_prefix_sources_finite R hQ
  letI : Finite (NonsymmetricSurvivingSources R hQ) := Subtype.finite
  letI : Finite (NonsymmetricErasedSources R hQ) := Subtype.finite
  letI : Finite (NonsymmetricFinalSources R) :=
    Finite.of_equiv _ (nonsymmetricSourceInsertionEquiv R hQ).symm
  have hf := Nat.card_congr (nonsymmetricSourceInsertionEquiv R hQ)
  have hp := Nat.card_congr (Equiv.sumCompl (fun s : NonsymmetricPrefixSources R hQ =>
    s.val-(actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ) ∈ (nsH R).asRelativeIdeal))
  change Nat.card (NonsymmetricErasedSources R hQ ⊕ NonsymmetricSurvivingSources R hQ)=
    (nonsymmetricPrefixIdeal R hQ).generatorCount at hp
  rw [Nat.card_sum] at hp
  rw [Nat.card_sum,Nat.card_eq_fintype_card (α := Unit),Fintype.card_unit,
    nonsymmetric_final_source_count_dictionary R] at hf
  unfold nonsymmetricDeltaSource nonsymmetricSourceLoss
  omega

theorem nonsymmetric_erasure_principal_pure_a (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (s : NonsymmetricErasedSources R hQ) :
    ∃ k : ℕ, actualPrincipalIndex P.M.base*normalizedM P.M.base=k*nsA R := by
  obtain ⟨ell,_,_,hs⟩ := nonsymmetric_erased_source_is_CENTER_O R hB hQ s
  have S := nonsymmetricReturnTuple_spec R hB ell
  have hd := nonsymmetric_return_depth_lt_c1 R hB ell.property.1 S.1 S.2.2.2.2.2.2
  have hn : nsC1 R-(nonsymmetricReturnTuple R hB ell).2.2 < nsC1 R := by omega
  obtain ⟨z,hz,he⟩ := s.property
  obtain ⟨a,b,c,hfac⟩ := L5A2C4OR6.routingH_factorization P.M.base (nsReindex R)
    (show actualPrincipalIndex P.M.base*normalizedM P.M.base ∈ nsH R from by
      rw [nonsymmetric_H_eq_normalizedH R]; exact (actualPrincipalIndex_spec P.M.base).2)
  obtain ⟨a',b',c',hzfac⟩ := L5A2C4OR6.routingH_factorization P.M.base (nsReindex R) hz
  change actualPrincipalIndex P.M.base*normalizedM P.M.base=a*nsA R+b*nsB R+c*nsC R at hfac
  change z=a'*nsA R+b'*nsB R+c'*nsC R at hzfac
  have eq : (nsC1 R-(nonsymmetricReturnTuple R hB ell).2.2)*nsA R=
      (a+a')*nsA R+(b+b')*nsB R+(c+c')*nsC R := by
    rw [hs] at he
    have heN : (nsC1 R-(nonsymmetricReturnTuple R hB ell).2.2)*nsA R=
        actualPrincipalIndex P.M.base*normalizedM P.M.base+z := by
      have hzEq : ((nsC1 R-(nonsymmetricReturnTuple R hB ell).2.2)*nsA R : ℕ)=
          (actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)+(z : ℤ) := by
        simpa only [nonsymmetricO] using (show (nonsymmetricO R
          (nonsymmetricReturnTuple R hB ell).2.2 : ℕ)=
          (actualPrincipalIndex P.M.base*normalizedM P.M.base : ℕ)+(z : ℤ) by omega)
      exact_mod_cast hzEq
    rw [heN,hfac,hzfac]
    ring
  have hc := nonsymmetric_subcritical_a_factorization R hn eq
  have hb0 : b=0 := by omega
  have hc0 : c=0 := by omega
  exact ⟨a,by simpa only [hb0,hc0,zero_mul,add_zero] using hfac⟩

private theorem return_residue (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (ell : NonsymmetricReturnIndex R) :
    gridResidue P.M.base (nsReindex R) (nonsymmetricReturnTuple R hB ell).1
      (nonsymmetricReturnTuple R hB ell).2.1=
      ((ell.val*normalizedM P.M.base : ℕ) : ZMod (nsA R)) := by
  have h := congrArg (fun n : ℕ => (n : ZMod (nsA R)))
    (nonsymmetricReturnTuple_spec R hB ell).2.2.2.2.2.2
  simpa only [gridResidue,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero] using h

theorem nonsymmetric_pure_principal_forbids_boundary_returns (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M)
    (hpure : ∃ k : ℕ, actualPrincipalIndex P.M.base*normalizedM P.M.base=k*nsA R) :
    ∀ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 ≠ nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 ≠ nsQ R := by
  obtain ⟨k,hk⟩ := hpure
  intro ell
  let comp : NonsymmetricReturnIndex R :=
    ⟨actualPrincipalIndex P.M.base-ell.val,by omega,by omega⟩
  have S := nonsymmetricReturnTuple_spec R hB ell
  have C := nonsymmetricReturnTuple_spec R hB comp
  have coeff := nonsymmetric_coefficients R
  have hre := return_residue R hB ell
  have hrc := return_residue R hB comp
  have hsum : gridResidue P.M.base (nsReindex R) (nonsymmetricReturnTuple R hB comp).1
      (nonsymmetricReturnTuple R hB comp).2.1+
      gridResidue P.M.base (nsReindex R) (nonsymmetricReturnTuple R hB ell).1
      (nonsymmetricReturnTuple R hB ell).2.1=0 := by
    rw [hre,hrc]
    have he : (actualPrincipalIndex P.M.base-ell.val)*normalizedM P.M.base+
        ell.val*normalizedM P.M.base=k*nsA R := by
      rw [← add_mul,Nat.sub_add_cancel (by omega),hk]
    have h := congrArg (fun n : ℕ => (n : ZMod (nsA R))) he
    simpa only [comp,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero] using h
  have hrel := congrArg (fun n : ℕ => (n : ZMod (nsA R))) (nonsymmetric_normalized_relations R).1
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero] at hrel
  constructor
  · intro hi
    have hj : (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R := by
      rcases S.1.2.2 with h | h
      · omega
      · exact h
    have dom : NonsymmetricLDomain R 0 (nsQ R-(nonsymmetricReturnTuple R hB ell).2.1) := by
      unfold NonsymmetricLDomain
      omega
    have hinv : gridResidue P.M.base (nsReindex R) (nonsymmetricReturnTuple R hB ell).1
        (nonsymmetricReturnTuple R hB ell).2.1+
        gridResidue P.M.base (nsReindex R) 0 (nsQ R-(nonsymmetricReturnTuple R hB ell).2.1)=0 := by
      have sub : (((nsQ R-(nonsymmetricReturnTuple R hB ell).2.1 : ℕ) : ZMod (nsA R)))+
          ((nonsymmetricReturnTuple R hB ell).2.1 : ZMod (nsA R))=nsQ R := by
        have hs := congrArg (fun n : ℕ => (n : ZMod (nsA R))) (Nat.sub_add_cancel (le_of_lt hj))
        simpa only [Nat.cast_add] using hs
      simp only [gridResidue,hi,Nat.cast_zero,zero_mul,zero_add]
      linear_combination -hrel + sub * (nsC R : ZMod (nsA R))
    have he : gridResidue P.M.base (nsReindex R) (nonsymmetricReturnTuple R hB comp).1
        (nonsymmetricReturnTuple R hB comp).2.1=
        gridResidue P.M.base (nsReindex R) 0 (nsQ R-(nonsymmetricReturnTuple R hB ell).2.1) := by
      linear_combination hsum-hinv
    have hc := nonsymmetric_lShape_grid_injective R C.1 dom he
    omega
  · intro hj
    have hi : (nonsymmetricReturnTuple R hB ell).1 < nsP R := by
      rcases S.1.2.2 with h | h
      · exact h
      · omega
    have dom : NonsymmetricLDomain R (nsP R-(nonsymmetricReturnTuple R hB ell).1) 0 := by
      unfold NonsymmetricLDomain
      omega
    have hinv : gridResidue P.M.base (nsReindex R) (nonsymmetricReturnTuple R hB ell).1
        (nonsymmetricReturnTuple R hB ell).2.1+
        gridResidue P.M.base (nsReindex R) (nsP R-(nonsymmetricReturnTuple R hB ell).1) 0=0 := by
      have sub : (((nsP R-(nonsymmetricReturnTuple R hB ell).1 : ℕ) : ZMod (nsA R)))+
          ((nonsymmetricReturnTuple R hB ell).1 : ZMod (nsA R))=nsP R := by
        have hs := congrArg (fun n : ℕ => (n : ZMod (nsA R))) (Nat.sub_add_cancel (le_of_lt hi))
        simpa only [Nat.cast_add] using hs
      simp only [gridResidue,hj,Nat.cast_zero,zero_mul,add_zero]
      linear_combination -hrel + sub * (nsB R : ZMod (nsA R))
    have he : gridResidue P.M.base (nsReindex R) (nonsymmetricReturnTuple R hB comp).1
        (nonsymmetricReturnTuple R hB comp).2.1=
        gridResidue P.M.base (nsReindex R) (nsP R-(nonsymmetricReturnTuple R hB ell).1) 0 := by
      linear_combination hsum-hinv
    have hc := nonsymmetric_lShape_grid_injective R C.1 dom he
    omega

theorem nonsymmetric_loss_eq_one_implies_FU_two (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (he : nonsymmetricSourceLoss R hQ=1) : nonsymmetricFU R hB=2 := by
  have hne : Nonempty (NonsymmetricErasedSources R hQ) :=
    (Nat.card_pos_iff.mp (show 0 < Nat.card (NonsymmetricErasedSources R hQ) by
      change 0 < nonsymmetricSourceLoss R hQ; rw [he]; exact Nat.zero_lt_one)).1
  obtain ⟨s⟩ := hne
  have hn := nonsymmetric_pure_principal_forbids_boundary_returns R hB
    (nonsymmetric_erasure_principal_pure_a R hB hQ s)
  have hl : nonsymmetricDL0 R hB=0 := by
    unfold nonsymmetricDL0 nonsymmetricReturnDepthMax
    apply le_antisymm _ (Nat.zero_le _)
    apply Finset.sup_le
    intro ell _
    simp only [ite_eq_right (hn ell).2]
    exact le_refl _
  have hr : nonsymmetricDR0 R hB=0 := by
    unfold nonsymmetricDR0 nonsymmetricReturnDepthMax
    apply le_antisymm _ (Nat.zero_le _)
    apply Finset.sup_le
    intro ell _
    simp only [ite_eq_right (hn ell).1]
    exact le_refl _
  simp only [nonsymmetricFU,hl,hr,Nat.zero_le,ite_eq_left,one_add_one_eq_two]

theorem nonsymmetric_balanced_actual_type_le_sourceCount (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) : Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  have hp := nonsymmetric_balanced_prefix_slack_bound R hB hQ hbal
  have ht := nonsymmetric_DeltaSocle_le_two R hB hQ
  have hs := nonsymmetric_DeltaSource_eq_one_sub_loss R hQ
  have he := nonsymmetric_source_loss_zero_or_one R hB hQ
  have hf := nonsymmetric_FU_one_or_two R hB
  have hw := nonsymmetric_signed_defect_identity R hQ
  rcases he with he | he
  · have heZ : (nonsymmetricSourceLoss R hQ : ℤ)=0 := by exact_mod_cast he
    rw [heZ] at hs
    rw [P2Data.W] at hw
    omega
  · have heZ : (nonsymmetricSourceLoss R hQ : ℤ)=1 := by exact_mod_cast he
    rw [heZ] at hs
    have hfu := nonsymmetric_loss_eq_one_implies_FU_two R hB hQ he
    rw [hfu] at hp
    rw [P2Data.W] at hw
    omega

end NS25Lean.L5A2BFinalRepair
