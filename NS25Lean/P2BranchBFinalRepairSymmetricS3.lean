import NS25Lean.P2BranchBFinalRepairSymmetricS8
import NS25Lean.P2SectorCLocalCollisionAccounting

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open FourGeneratedBridge ChosenBase L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR4R2A L5A2B4AR5A L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4C
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The actual coordinate-minimal return points, not a presumed chart. -/
abbrev SymmetricMinimalFPoints (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M) :=
  {xy : ℕ×ℕ //
    (∃ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).1=xy.1 ∧ (symmetricReturnTuple A hB ell).2.1=xy.2) ∧
    ∀ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).1 ≤ xy.1 → (symmetricReturnTuple A hB ell).2.1 ≤ xy.2 →
      (symmetricReturnTuple A hB ell).1=xy.1 ∧ (symmetricReturnTuple A hB ell).2.1=xy.2}

theorem symmetric_minimal_F_bounds (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (p : SymmetricMinimalFPoints A hB) :
    0 < p.val.1 ∧ p.val.1 < ciH A ∧ 0 < p.val.2 ∧ p.val.2 < ciG A := by
  obtain ⟨ell,hi,hj⟩ := p.property.1
  have S := symmetricReturnTuple_spec A hB ell
  simpa only [hi,hj] using (show 0 < (symmetricReturnTuple A hB ell).1 ∧
    (symmetricReturnTuple A hB ell).1 < ciH A ∧ 0 < (symmetricReturnTuple A hB ell).2.1 ∧
    (symmetricReturnTuple A hB ell).2.1 < ciG A from ⟨S.1,S.2.1,S.2.2.1,S.2.2.2.1⟩)

theorem symmetric_minimal_F_antichain (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (p q : SymmetricMinimalFPoints A hB) (hx : p.val.1 ≤ q.val.1) (hy : p.val.2 ≤ q.val.2) : p=q := by
  obtain ⟨ell,hi,hj⟩ := p.property.1
  have h := q.property.2 ell (by omega) (by omega)
  apply Subtype.ext
  exact Prod.ext (by omega) (by omega)

theorem symmetric_minimal_F_x_injective (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M) :
    Function.Injective (fun p : SymmetricMinimalFPoints A hB => p.val.1) := by
  intro p q hx
  change p.val.1=q.val.1 at hx
  rcases le_total p.val.2 q.val.2 with hy | hy
  · exact symmetric_minimal_F_antichain A hB p q (by omega) hy
  · exact (symmetric_minimal_F_antichain A hB q p (by omega) hy).symm

theorem symmetric_minimal_F_y_injective (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M) :
    Function.Injective (fun p : SymmetricMinimalFPoints A hB => p.val.2) := by
  intro p q hy
  change p.val.2=q.val.2 at hy
  rcases le_total p.val.1 q.val.1 with hx | hx
  · exact symmetric_minimal_F_antichain A hB p q hx (by omega)
  · exact (symmetric_minimal_F_antichain A hB q p hx (by omega)).symm

instance symmetric_minimal_F_finite (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M) :
    Finite (SymmetricMinimalFPoints A hB) :=
  Finite.of_injective (fun p => (⟨p.val.1,(symmetric_minimal_F_bounds A hB p).2.1⟩ : Fin (ciH A)))
    (fun _ _ h => symmetric_minimal_F_x_injective A hB (congrArg Fin.val h))

theorem symmetric_return_dominated_by_minimal_F (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (ell : SymmetricReturnIndex A) :
    ∃ p : SymmetricMinimalFPoints A hB,
      p.val.1 ≤ (symmetricReturnTuple A hB ell).1 ∧
      p.val.2 ≤ (symmetricReturnTuple A hB ell).2.1 := by
  let T := {l : SymmetricReturnIndex A // (symmetricReturnTuple A hB l).1 ≤
      (symmetricReturnTuple A hB ell).1 ∧ (symmetricReturnTuple A hB l).2.1 ≤
      (symmetricReturnTuple A hB ell).2.1}
  have hn : Nonempty T := ⟨⟨ell,le_refl _,le_refl _⟩⟩
  let f := fun l : T => (symmetricReturnTuple A hB l.val).1+(symmetricReturnTuple A hB l.val).2.1
  obtain ⟨k,hk⟩ := natMinImage_spec hn f
  refine ⟨⟨((symmetricReturnTuple A hB k.val).1,(symmetricReturnTuple A hB k.val).2.1),
    ⟨⟨k.val,rfl,rfl⟩,?_⟩⟩,k.property⟩
  intro l hi hj
  let lt : T := ⟨l,le_trans hi k.property.1,le_trans hj k.property.2⟩
  have hm := natMinImage_le hn f lt
  rw [← hk] at hm
  change (symmetricReturnTuple A hB k.val).1+(symmetricReturnTuple A hB k.val).2.1 ≤
    (symmetricReturnTuple A hB l).1+(symmetricReturnTuple A hB l).2.1 at hm
  constructor <;> omega

abbrev SymmetricNextF (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (p : SymmetricMinimalFPoints A hB) := {q : SymmetricMinimalFPoints A hB // p.val.1 < q.val.1}

def symmetricNextF (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (p : SymmetricMinimalFPoints A hB) (hn : Nonempty (SymmetricNextF A hB p)) :
    SymmetricNextF A hB p :=
  Classical.choose (natMinImage_spec hn (fun q => q.val.val.1))

theorem symmetricNextF_min (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (p : SymmetricMinimalFPoints A hB) (hn : Nonempty (SymmetricNextF A hB p))
    (q : SymmetricNextF A hB p) : (symmetricNextF A hB p hn).val.val.1 ≤ q.val.val.1 := by
  have hs := Classical.choose_spec (natMinImage_spec hn (fun q => q.val.val.1))
  change (symmetricNextF A hB p hn).val.val.1=natMinImage hn (fun q => q.val.val.1) at hs
  rw [hs]
  exact natMinImage_le hn (fun q => q.val.val.1) q

theorem symmetricNextF_y_drop (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (p : SymmetricMinimalFPoints A hB) (hn : Nonempty (SymmetricNextF A hB p)) :
    (symmetricNextF A hB p hn).val.val.2 < p.val.2 := by
  let q := symmetricNextF A hB p hn
  change q.val.val.2 < p.val.2
  have hx := q.property
  by_contra hy
  have he := symmetric_minimal_F_antichain A hB p q.val (by omega) (by omega)
  have hv := congrArg (fun p : SymmetricMinimalFPoints A hB => p.val.1) he
  omega

theorem symmetric_minimal_F_next_notch_unused (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : SymmetricMinimalFPoints A hB) (hn : Nonempty (SymmetricNextF A hB p)) :
    L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (symmetricPrefixRouting A hQ)
      (gridResidue P.M.base A.reindex ((symmetricNextF A hB p hn).val.val.1-1) (p.val.2-1)) := by
  let q := symmetricNextF A hB p hn
  have hp := symmetric_minimal_F_bounds A hB p
  have hq := symmetric_minimal_F_bounds A hB q.val
  have hxd := q.property
  have hyd : q.val.val.2 < p.val.2 := symmetricNextF_y_drop A hB p hn
  change L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (symmetricPrefixRouting A hQ)
    (gridResidue P.M.base A.reindex (q.val.val.1-1) (p.val.2-1))
  apply symmetric_prefix_ordinary_notch_unused A hB hQ
    (x := q.val.val.1-1) (y := p.val.2-1) (by omega) (by omega)
  · intro ell he
    obtain ⟨z,hzi,hzj⟩ := symmetric_return_dominated_by_minimal_F A hB ell
    have hzx : z.val.1 ≤ q.val.val.1-1 := by omega
    have hzy : z.val.2 ≤ p.val.2-1 := by omega
    by_cases hpx : z.val.1 ≤ p.val.1
    · have heq := symmetric_minimal_F_antichain A hB z p hpx (by omega)
      have hy := congrArg (fun z : SymmetricMinimalFPoints A hB => z.val.2) heq
      omega
    · have hmin := symmetricNextF_min A hB p hn ⟨z,by omega⟩
      change q.val.val.1 ≤ z.val.1 at hmin
      omega
  · obtain ⟨ell,hi,hj⟩ := q.val.property.1
    exact ⟨ell,by omega,by omega⟩
  · obtain ⟨ell,hi,hj⟩ := p.property.1
    exact ⟨ell,by omega,by omega⟩

private theorem grid_injective (A : SectorBCriticalRoleBranchA P)
    {x y x' y' : ℕ} (hx : x < ciH A) (hy : y < ciG A)
    (hx' : x' < ciH A) (hy' : y' < ciG A)
    (he : gridResidue P.M.base A.reindex x y=gridResidue P.M.base A.reindex x' y') :
    x=x' ∧ y=y' := by
  apply branchA_rectangle_modEq_unique A hx hy hx' hy'
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa only [gridResidue,Nat.cast_add,Nat.cast_mul] using he

/-- A resource for each actual minimal F point: the adjacent notch,
or the extra corner at the last point. -/
def symmetricFUnusedResource (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (p : SymmetricMinimalFPoints A hB) :
    {r : ZMod (routingA P.M.base A.reindex) //
      L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (symmetricPrefixRouting A hQ) r} := by
  classical
  exact if hn : Nonempty (SymmetricNextF A hB p) then
    ⟨gridResidue P.M.base A.reindex ((symmetricNextF A hB p hn).val.val.1-1) (p.val.2-1),
      symmetric_minimal_F_next_notch_unused A hB hQ p hn⟩
    else ⟨gridResidue P.M.base A.reindex (ciH A-1) (ciG A-1),symmetric_prefix_kappa_unused A hB hQ⟩

theorem symmetricFUnusedResource_injective (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Function.Injective (symmetricFUnusedResource A hB hQ) := by
  classical
  intro p q he
  have hp := symmetric_minimal_F_bounds A hB p
  have hq := symmetric_minimal_F_bounds A hB q
  have hv := congrArg Subtype.val he
  dsimp only [symmetricFUnusedResource] at hv
  by_cases hpn : Nonempty (SymmetricNextF A hB p)
  · rw [dif_pos hpn] at hv
    have hnP := symmetric_minimal_F_bounds A hB (symmetricNextF A hB p hpn).val
    by_cases hqn : Nonempty (SymmetricNextF A hB q)
    · rw [dif_pos hqn] at hv
      have hnQ := symmetric_minimal_F_bounds A hB (symmetricNextF A hB q hqn).val
      have hc := grid_injective A (by omega) (by omega) (by omega) (by omega) hv
      apply symmetric_minimal_F_y_injective A hB
      change p.val.2=q.val.2
      omega
    · rw [dif_neg hqn] at hv
      have hg := (symmetric_ci_normalized_equations A).1
      have hh := (symmetric_ci_normalized_equations A).2.1
      have hc := grid_injective A (by omega) (by omega) (by omega) (by omega) hv
      omega
  · rw [dif_neg hpn] at hv
    by_cases hqn : Nonempty (SymmetricNextF A hB q)
    · rw [dif_pos hqn] at hv
      have hnQ := symmetric_minimal_F_bounds A hB (symmetricNextF A hB q hqn).val
      have hg := (symmetric_ci_normalized_equations A).1
      have hh := (symmetric_ci_normalized_equations A).2.1
      have hc := grid_injective A (by omega) (by omega) (by omega) (by omega) hv
      omega
    · apply symmetric_minimal_F_x_injective A hB
      change p.val.1=q.val.1
      by_cases hlt : p.val.1 < q.val.1
      · exact False.elim (hpn ⟨⟨q,hlt⟩⟩)
      by_cases hgt : q.val.1 < p.val.1
      · exact False.elim (hqn ⟨⟨p,hgt⟩⟩)
      omega

theorem symmetric_prefix_unused_count_ge_minimal_F (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Nat.card (SymmetricMinimalFPoints A hB) ≤
      Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases (symmetricPrefixRouting A hQ)) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  letI : Finite (L5A2C4I.ResidueData.ExactUnusedMergeBases (symmetricPrefixRouting A hQ)) := Subtype.finite
  exact Nat.card_le_card_of_injective _ (symmetricFUnusedResource_injective A hB hQ)

private theorem gridH (A : SectorBCriticalRoleBranchA P) (p q t : ℕ) :
    ((p*n0 A+q*n1 A+t*n2 A : ℕ) : ℤ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal := by
  refine ⟨_,?_,rfl⟩
  change _ ∈ generatedThree (routingA P.M.base A.reindex)
    (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
  rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A]
  exact (mem_generatedThree_iff _ _ _ _).mpr ⟨p,q,t,rfl⟩

private theorem minimal_eq_divisor (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) {z g : ℤ}
    (hz : (symmetricPrefixIdeal A hQ).IsMinimalGenerator z)
    (hg : g ∈ symmetricPrefixIdeal A hQ)
    (hd : z-g ∈ (routingH P.M.base A.reindex).asRelativeIdeal) : z=g := by
  obtain ⟨n,hn,he⟩ := hd
  by_cases h : n=0
  · subst n
    simp only [Nat.cast_zero] at he
    omega
  · apply False.elim
    apply hz.2 n hn h
    convert hg using 1 <;> omega

theorem symmetric_prefix_C_target_minimal_F (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 2 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    let hQ1 : 1 < actualPrincipalIndex P.M.base := by omega
    ∀ r, (symmetricPrefixRouting A hQ1).IsBranch r →
      (symmetricPrefixRouting A hQ1).IsSource ((symmetricPrefixRouting A hQ1).branchTarget r) →
      ∃ p : SymmetricMinimalFPoints A hB,
        symmetricPrefixLambda A hQ1 ((symmetricPrefixRouting A hQ1).branchTarget r)=
          (p.val.1*n1 A+p.val.2*n2 A : ℕ) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  dsimp only
  let hQ1 : 1 < actualPrincipalIndex P.M.base := by omega
  intro r hr hs
  obtain ⟨ell,he⟩ := symmetric_prefix_C_targets_F A hB hQ r hr hs
  change symmetricPrefixLambda A hQ1 ((symmetricPrefixRouting A hQ1).branchTarget r)=
    (symmetricF A (symmetricReturnTuple A hB ell).1 (symmetricReturnTuple A hB ell).2.1 : ℤ) at he
  obtain ⟨p,hpi,hpj⟩ := symmetric_return_dominated_by_minimal_F A hB ell
  obtain ⟨lp,hli,hlj⟩ := p.property.1
  have S := symmetricReturnTuple_spec A hB lp
  have hg : ((p.val.1*n1 A+p.val.2*n2 A : ℕ) : ℤ) ∈ symmetricPrefixIdeal A hQ1 := by
    refine ⟨lp.val,lp.property.1,lp.property.2,?_⟩
    simpa only [symmetricF,hli,hlj] using
      (symmetric_single_return_sources_mem A hB lp.property.1 S.2.1 S.2.2.2.1 S.2.2.2.2.2.2.2).1
  have hgen := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base A.reindex)).1
  have hm := ((symmetricPrefixIdeal A hQ1).concrete_isSource_iff_isMinimalGenerator
    (routingA P.M.base A.reindex) (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
    hgen (routingHB _ _) (routingHC _ _)
    (by rw [routingB_eq_n1 A]; exact (branchA_symmetricTailData A).n1_pos.ne')
    (by rw [routingC_eq_n2 A]; exact (branchA_symmetricTailData A).n2_pos.ne') _).mp hs
  have hd : symmetricPrefixLambda A hQ1 ((symmetricPrefixRouting A hQ1).branchTarget r)-
      (p.val.1*n1 A+p.val.2*n2 A : ℕ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal := by
    rw [he]
    have hdi : (((symmetricReturnTuple A hB ell).1-p.val.1 : ℕ) : ℤ)+p.val.1=
        (symmetricReturnTuple A hB ell).1 := by exact_mod_cast Nat.sub_add_cancel hpi
    have hdj : (((symmetricReturnTuple A hB ell).2.1-p.val.2 : ℕ) : ℤ)+p.val.2=
        (symmetricReturnTuple A hB ell).2.1 := by exact_mod_cast Nat.sub_add_cancel hpj
    have hmem := gridH A 0 ((symmetricReturnTuple A hB ell).1-p.val.1)
      ((symmetricReturnTuple A hB ell).2.1-p.val.2)
    convert hmem using 1
    simp only [symmetricF,Nat.cast_add,Nat.cast_mul,zero_mul,zero_add]
    nlinarith only [hdi,hdj]
  exact ⟨p,minimal_eq_divisor A hQ1 hm hg hd⟩

def symmetricCBranchFPoint (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 2 < actualPrincipalIndex P.M.base)
    (s : L5A2C4I.ResidueData.CSourceTargetBranches
      (symmetricPrefixRouting A (by omega : 1 < actualPrincipalIndex P.M.base))) :
    SymmetricMinimalFPoints A hB :=
  Classical.choose (symmetric_prefix_C_target_minimal_F A hB hQ s.val s.property.1 s.property.2)

theorem symmetricCBranchFPoint_injective (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 2 < actualPrincipalIndex P.M.base) : Function.Injective (symmetricCBranchFPoint A hB hQ) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  let hQ1 : 1 < actualPrincipalIndex P.M.base := by omega
  intro s t he
  have hs := Classical.choose_spec (symmetric_prefix_C_target_minimal_F A hB hQ s.val s.property.1 s.property.2)
  have ht := Classical.choose_spec (symmetric_prefix_C_target_minimal_F A hB hQ t.val t.property.1 t.property.2)
  change symmetricPrefixLambda A hQ1 ((symmetricPrefixRouting A hQ1).branchTarget s.val)=
    ((symmetricCBranchFPoint A hB hQ s).val.1*n1 A+(symmetricCBranchFPoint A hB hQ s).val.2*n2 A : ℕ) at hs
  change symmetricPrefixLambda A hQ1 ((symmetricPrefixRouting A hQ1).branchTarget t.val)=
    ((symmetricCBranchFPoint A hB hQ t).val.1*n1 A+(symmetricCBranchFPoint A hB hQ t).val.2*n2 A : ℕ) at ht
  rw [he] at hs
  have hv := hs.trans ht.symm
  have hmod := congrArg (fun v : ℤ => (v : ZMod (routingA P.M.base A.reindex))) hv
  simp only [symmetricPrefixLambda,RelativeIdeal.aperyRepresentative_mod] at hmod
  exact Subtype.ext ((symmetricPrefixRouting A hQ1).branchTarget_injective hmod)

theorem symmetric_prefix_C_count_le_minimal_F (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 2 < actualPrincipalIndex P.M.base) :
    L5A2C4I.ResidueData.sourceTargetBranchCount
      (symmetricPrefixRouting A (by omega : 1 < actualPrincipalIndex P.M.base)) ≤
      Nat.card (SymmetricMinimalFPoints A hB) :=
  Nat.card_le_card_of_injective _ (symmetricCBranchFPoint_injective A hB hQ)

theorem symmetric_prefix_resource_bounds (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 2 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    let hQ1 : 1 < actualPrincipalIndex P.M.base := by omega
    let D := symmetricPrefixRouting A hQ1
    let r := Nat.card (SymmetricMinimalFPoints A hB)
    L5A2C4I.ResidueData.sourceTargetBranchCount D ≤ r ∧
      r ≤ Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases D) ∧
      fakeSinkCount (symmetricPrefixIdeal A hQ1) (routingA P.M.base A.reindex)
        (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _)=1 := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  dsimp only
  exact ⟨symmetric_prefix_C_count_le_minimal_F A hB hQ,
    symmetric_prefix_unused_count_ge_minimal_F A hB (by omega),
    symmetric_prefix_fakeSinkCount_eq_one A hB (by omega)⟩

theorem symmetric_prefix_raw_slack_identity (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    let D := symmetricPrefixRouting A hQ
    (actualSinkCount (symmetricPrefixIdeal A hQ) (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _) : ℤ)-
      D.sourceCount = (L5A2C4I.ResidueData.sourceTargetBranchCount D : ℤ)-
        Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases D)-
        fakeSinkCount (symmetricPrefixIdeal A hQ) (routingA P.M.base A.reindex)
          (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  let D := symmetricPrefixRouting A hQ
  have hbalance := CombinatorialCore.ResidueData.edge_count_balance D.outgoing_edge_count D.incoming_edge_count
  have hb := L5A2C4J.ResidueData.branchCount_raw_decomposition D
  have hm := L5A2C4J.ResidueData.mergeCount_raw_decomposition D
  have hs := fullSinkCount_eq_actual_add_fake (symmetricPrefixIdeal A hQ)
    (routingA P.M.base A.reindex) (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
    (routingHB _ _) (routingHC _ _)
  change D.sinkCount = actualSinkCount (symmetricPrefixIdeal A hQ) (routingA P.M.base A.reindex)
    (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _)+
    fakeSinkCount (symmetricPrefixIdeal A hQ) (routingA P.M.base A.reindex)
    (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _) at hs
  unfold L5A2C4J.ResidueData.exactUnusedMergeCount at hm
  dsimp only
  dsimp only [D] at hbalance hb hm hs
  omega

theorem symmetric_prefix_slack_le_neg_one (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 2 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    let hQ1 : 1 < actualPrincipalIndex P.M.base := by omega
    (actualSinkCount (symmetricPrefixIdeal A hQ1) (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _) : ℤ)-
      (symmetricPrefixRouting A hQ1).sourceCount ≤ -1 := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  have hs := symmetric_prefix_raw_slack_identity A (by omega : 1 < actualPrincipalIndex P.M.base)
  have hr := symmetric_prefix_resource_bounds A hB hQ
  dsimp only at hr hs ⊢
  omega

theorem symmetric_prefix_sourceCount_eq_prefix_sources (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    (symmetricPrefixRouting A hQ).sourceCount=Nat.card (symmetricPrefixSources A) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  have hgen := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base A.reindex)).1
  exact (symmetricPrefixIdeal A hQ).concrete_sourceCount_eq_generatorCount
    (routingA P.M.base A.reindex) (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
    hgen (routingHB _ _) (routingHC _ _)
    (by rw [routingB_eq_n1 A]; exact (branchA_symmetricTailData A).n1_pos.ne')
    (by rw [routingC_eq_n2 A]; exact (branchA_symmetricTailData A).n2_pos.ne')

theorem symmetric_prefix_actual_socle_count_bound (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 2 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    let hQ1 : 1 < actualPrincipalIndex P.M.base := by omega
    actualSinkCount (symmetricPrefixIdeal A hQ1) (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _)+1 ≤
      Nat.card (symmetricPrefixSources A) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  have hs := symmetric_prefix_slack_le_neg_one A hB hQ
  have he := symmetric_prefix_sourceCount_eq_prefix_sources A (by omega : 1 < actualPrincipalIndex P.M.base)
  dsimp only at hs ⊢
  rw [he] at hs
  omega

theorem symmetric_final_sources_card_eq_actual_sourceCount (A : SectorBCriticalRoleBranchA P) :
    Nat.card (symmetricFinalSources A)=P.sourceCount := by
  have he : Nat.card (symmetricFinalSources A)=(normalizedI P.M.base).generatorCount := by
    simp only [symmetricFinalSources,symmetric_routingH_eq_normalizedH A]
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

theorem symmetric_actual_source_count_insertion (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    P.sourceCount=Nat.card (symmetricPrefixSources A)+1 := by
  rw [← symmetric_final_sources_card_eq_actual_sourceCount A]
  exact symmetric_source_count_insertion A hB hQ

theorem symmetric_prefix_socle_plus_two_le_actual_sourceCount (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 2 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    let hQ1 : 1 < actualPrincipalIndex P.M.base := by omega
    actualSinkCount (symmetricPrefixIdeal A hQ1) (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _)+2 ≤
      P.sourceCount := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  have hp := symmetric_prefix_actual_socle_count_bound A hB hQ
  have hs := symmetric_actual_source_count_insertion A hB (by omega : 1 < actualPrincipalIndex P.M.base)
  dsimp only at hp ⊢
  omega

end NS25Lean.L5A2BFinalRepair
