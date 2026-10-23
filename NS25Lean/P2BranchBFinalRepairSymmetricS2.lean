import NS25Lean.P2BranchBFinalRepairSymmetric

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open FourGeneratedBridge ChosenBase L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR4R2A L5A2B4AR5A L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4C
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

private theorem gridH (A : SectorBCriticalRoleBranchA P) (p q t : ℕ) :
    ((p*n0 A+q*n1 A+t*n2 A : ℕ) : ℤ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal := by
  refine ⟨_,?_,rfl⟩
  change _ ∈ generatedThree (routingA P.M.base A.reindex)
    (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
  rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A]
  exact (mem_generatedThree_iff _ _ _ _).mpr ⟨p,q,t,rfl⟩

private theorem canonical_no_a (A : SectorBCriticalRoleBranchA P)
    {x y : ℕ} (hx : x < ciH A) (hy : y < ciG A) :
    ((x*n1 A+y*n2 A : ℕ) : ℤ)-n0 A ∉ (routingH P.M.base A.reindex).asRelativeIdeal := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  have hc := symmetric_ci_rectangle_canonical A hx hy
  change ((normalizedGrid P.M.base A.reindex 0 x y : ℕ) : ℤ)=
    (routingH P.M.base A.reindex).asRelativeIdeal.aperyRepresentative
      (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex x y) at hc
  have hn := (routingH P.M.base A.reindex).asRelativeIdeal.aperyRepresentative_sub_modulus_not_mem
    (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex x y)
  rw [← hc] at hn
  simpa only [normalizedGrid,zero_mul,zero_add,Nat.cast_add,Nat.cast_mul,
    routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A] using hn

private theorem canonical_factorization (A : SectorBCriticalRoleBranchA P)
    {x y p q t : ℕ} (hx : x < ciH A) (hy : y < ciG A)
    (he : x*n1 A+y*n2 A=p*n0 A+q*n1 A+t*n2 A) :
    p=0 ∧ q=x ∧ t=y := by
  have hn := canonical_no_a A hx hy
  have S := branchA_symmetricTailData A
  have hz (p' q' t' : ℕ)
      (h : x*n1 A+y*n2 A=(p'+1)*n0 A+q'*n1 A+t'*n2 A) : False := by
    apply hn
    have hm := gridH A p' q' t'
    have hZ := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hZ hm ⊢
    convert hm using 1 <;> nlinarith only [hZ]
  have hp : p=0 := by
    by_contra hp
    apply hz (p-1) q t
    have hp1 : p=p-1+1 := by omega
    simpa only [← hp1] using he
  have hq : q < ciH A := by
    by_contra hq
    have hk := (symmetric_ci_normalized_equations A).2.2.1
    apply hz (p+ciK A-1) (q-ciH A) t
    have hq1 : q=q-ciH A+ciH A := by omega
    have hp1 : p+ciK A=p+ciK A-1+1 := by omega
    calc
      _ = p*n0 A+(q-ciH A+ciH A)*n1 A+t*n2 A := by rw [← hq1]; exact he
      _ = (p+ciK A)*n0 A+(q-ciH A)*n1 A+t*n2 A := by
        rw [add_mul,symmetric_ci_b_carry A]; ring
      _ = _ := by rw [← hp1]
  have ht : t < ciG A := by
    by_contra ht
    apply hz (p+r A-1) (q+s A) (t-ciG A)
    have ht1 : t=t-ciG A+ciG A := by omega
    have hp1 : p+r A=p+r A-1+1 := by have := S.r_pos; omega
    calc
      _ = p*n0 A+q*n1 A+(t-ciG A+ciG A)*n2 A := by rw [← ht1]; exact he
      _ = (p+r A)*n0 A+(q+s A)*n1 A+(t-ciG A)*n2 A := by
        rw [add_mul,S.mixed_relation]; ring
      _ = _ := by rw [← hp1]
  have hmod : q*routingB P.M.base A.reindex+t*routingC P.M.base A.reindex ≡
      x*routingB P.M.base A.reindex+y*routingC P.M.base A.reindex
      [MOD routingA P.M.base A.reindex] := by
    rw [routingB_eq_n1 A,routingC_eq_n2 A]
    have he' := he
    simp only [hp,zero_mul,zero_add] at he'
    exact he'.symm ▸ Nat.ModEq.refl _
  have hc := branchA_rectangle_modEq_unique A hq ht hx hy hmod
  exact ⟨hp,hc⟩

/-- Canonical F divisibility has actual coordinate dominance; no support/family
identification or depth inequality is assumed. -/
theorem symmetric_canonical_F_divisor_coordinates (A : SectorBCriticalRoleBranchA P)
    {x y i j : ℕ} (hx : x < ciH A) (hy : y < ciG A)
    (hd : ((x*n1 A+y*n2 A : ℕ) : ℤ)-(i*n1 A+j*n2 A : ℕ) ∈
      (routingH P.M.base A.reindex).asRelativeIdeal) : i ≤ x ∧ j ≤ y := by
  obtain ⟨w,hw,he⟩ := hd
  change w ∈ generatedThree (routingA P.M.base A.reindex)
    (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) at hw
  rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A] at hw
  obtain ⟨p,q,t,hf⟩ := (mem_generatedThree_iff _ _ _ _).mp hw
  have heN : x*n1 A+y*n2 A=p*n0 A+(i+q)*n1 A+(j+t)*n2 A := by
    rw [hf] at he
    have heZ := he
    simp only [Nat.cast_add,Nat.cast_mul] at heZ
    exact_mod_cast (show (x : ℤ)*n1 A+y*n2 A=
      (p : ℤ)*n0 A+(i+q)*n1 A+(j+t)*n2 A by nlinarith only [heZ])
  have hc := canonical_factorization A hx hy heN
  omega

local instance (A : SectorBCriticalRoleBranchA P) : NeZero (routingA P.M.base A.reindex) :=
  ⟨(routingA_pos _ _).ne'⟩

abbrev symmetricPrefixLambda (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  (symmetricPrefixIdeal A hQ).aperyRepresentative (routingA P.M.base A.reindex)

private theorem canonical_prefix_coords (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) {x y : ℕ} (hx : x < ciH A) (hy : y < ciG A)
    (hz : ((x*n1 A+y*n2 A : ℕ) : ℤ) ∈
      prefixCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base)) :
    ∃ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).1 ≤ x ∧ (symmetricReturnTuple A hB ell).2.1 ≤ y := by
  obtain ⟨ell,hd⟩ := symmetric_canonical_prefix_F_divisor A hB hx hy hz
  exact ⟨ell,symmetric_canonical_F_divisor_coordinates A hx hy hd⟩

private theorem nat_grid_mod (A : SectorBCriticalRoleBranchA P) (l x y : ℕ) :
    ((l*n0 A+x*n1 A+y*n2 A : ℕ) : ZMod (routingA P.M.base A.reindex))=
      gridResidue P.M.base A.reindex x y := by
  simpa only [normalizedGrid,routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A] using
    normalizedGrid_mod P.M.base A.reindex l x y

/-- The inverse-X b-successor bound in the actual prefix Apéry chart. -/
theorem symmetric_prefix_inverseX_threshold (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    {x y : ℕ} (hx : x < ciH A) (hy : y < ciG A)
    (hz : ((x*n1 A+y*n2 A : ℕ) : ℤ) ∈ symmetricPrefixIdeal A hQ) :
    symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex 0 y) <
      (ciK A : ℤ)*n0 A+y*n2 A := by
  obtain ⟨ell,hi,hj⟩ := canonical_prefix_coords A hB hx hy hz
  have S := symmetricReturnTuple_spec A hB ell
  have hm := (symmetric_single_return_sources_mem A hB ell.property.1
    S.2.1 S.2.2.2.1 S.2.2.2.2.2.2.2).2.1
  have hdelta := gridH A 0 0 (y-(symmetricReturnTuple A hB ell).2.1)
  obtain ⟨n,hn,hne⟩ := hdelta
  have hp : (symmetricX A (symmetricReturnTuple A hB ell).2.1
      (symmetricReturnTuple A hB ell).2.2 : ℤ)+n ∈ symmetricPrefixIdeal A hQ :=
    ⟨ell.val,ell.property.1,ell.property.2,(returnIdeal _ _).add_mem hm hn⟩
  have hjZ : ((y-(symmetricReturnTuple A hB ell).2.1 : ℕ) : ℤ)+
      (symmetricReturnTuple A hB ell).2.1=y := by exact_mod_cast Nat.sub_add_cancel hj
  have he : (symmetricX A (symmetricReturnTuple A hB ell).2.1
      (symmetricReturnTuple A hB ell).2.2 : ℤ)+n=
      (((ciK A-(symmetricReturnTuple A hB ell).2.2)*n0 A+y*n2 A : ℕ) : ℤ) := by
    simp only [zero_mul,zero_add,Nat.cast_mul] at hne
    simp only [symmetricX,Nat.cast_add,Nat.cast_mul]
    nlinarith only [hne,hjZ]
  rw [he] at hp
  have hmod := nat_grid_mod A (ciK A-(symmetricReturnTuple A hB ell).2.2) 0 y
  simp only [zero_mul,add_zero] at hmod
  have hl := (symmetricPrefixIdeal A hQ).aperyRepresentative_le
    (routingA P.M.base A.reindex) _ hp (by exact_mod_cast hmod)
  have hd := S.2.2.2.2.1
  have hk := S.2.2.2.2.2.1
  have ha : (0 : ℤ)<n0 A := by exact_mod_cast (branchA_symmetricTailData A).n0_pos
  have hkZ : ((ciK A-(symmetricReturnTuple A hB ell).2.2 : ℕ) : ℤ)+
      (symmetricReturnTuple A hB ell).2.2=ciK A := by exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hk)
  simp only [Nat.cast_add,Nat.cast_mul] at hl
  change _ < _
  nlinarith

/-- The inverse-Y c-successor bound includes the extra b-wrap exactly. -/
theorem symmetric_prefix_inverseY_threshold (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    {x y : ℕ} (hx : x < ciH A) (hy : y < ciG A)
    (hz : ((x*n1 A+y*n2 A : ℕ) : ℤ) ∈ symmetricPrefixIdeal A hQ) :
    symmetricPrefixLambda A hQ
        (gridResidue P.M.base A.reindex ((x+ciV A)%ciH A) 0) <
      ((ciU A+(x+ciV A)/ciH A*ciK A : ℕ) : ℤ)*n0 A+
        (((x+ciV A)%ciH A : ℕ) : ℤ)*n1 A := by
  obtain ⟨ell,hi,hj⟩ := canonical_prefix_coords A hB hx hy hz
  have S := symmetricReturnTuple_spec A hB ell
  have hm := (symmetric_single_return_sources_mem A hB ell.property.1
    S.2.1 S.2.2.2.1 S.2.2.2.2.2.2.2).2.2
  have hdelta := gridH A 0 (x-(symmetricReturnTuple A hB ell).1) 0
  obtain ⟨n,hn,hne⟩ := hdelta
  have hp : (symmetricY A (symmetricReturnTuple A hB ell).1
      (symmetricReturnTuple A hB ell).2.2 : ℤ)+n ∈ symmetricPrefixIdeal A hQ :=
    ⟨ell.val,ell.property.1,ell.property.2,(returnIdeal _ _).add_mem hm hn⟩
  have hcost : (symmetricReturnTuple A hB ell).2.2 < ciU A+(x+ciV A)/ciH A*ciK A := by
    have hdiv := Nat.div_le_div_right (c := ciH A) (Nat.add_le_add_right hi (ciV A))
    exact lt_of_lt_of_le S.2.2.2.2.2.2.1
      (Nat.add_le_add_left (Nat.mul_le_mul_right (ciK A) hdiv) (ciU A))
  have hiZ : ((x-(symmetricReturnTuple A hB ell).1 : ℕ) : ℤ)+
      (symmetricReturnTuple A hB ell).1=x := by exact_mod_cast Nat.sub_add_cancel hi
  have hr := symmetric_ci_c_carry A (symmetricReturnTuple A hB ell).1
  have hrx := symmetric_ci_c_carry A x
  have hd := S.2.2.2.2.2.2.1
  have hsub := Nat.sub_add_cancel (Nat.le_of_lt hd)
  have hsubx := Nat.sub_add_cancel (Nat.le_of_lt hcost)
  have he : (symmetricY A (symmetricReturnTuple A hB ell).1
      (symmetricReturnTuple A hB ell).2.2 : ℤ)+n=
      (((ciU A+(x+ciV A)/ciH A*ciK A-(symmetricReturnTuple A hB ell).2.2)*n0 A+
        ((x+ciV A)%ciH A)*n1 A : ℕ) : ℤ) := by
    have hrZ := congrArg (fun t : ℕ => (t : ℤ)) hr
    have hrxZ := congrArg (fun t : ℕ => (t : ℤ)) hrx
    have hsZ := congrArg (fun t : ℕ => (t : ℤ)) hsub
    have hsxZ := congrArg (fun t : ℕ => (t : ℤ)) hsubx
    simp only [Nat.cast_add,Nat.cast_mul] at hrZ hrxZ hsZ hsxZ
    simp only [zero_mul,add_zero,zero_add,Nat.cast_mul] at hne
    simp only [symmetricY,Nat.cast_add,Nat.cast_mul]
    nlinarith only [hrZ,hrxZ,hsZ,hsxZ,hiZ,hne]
  rw [he] at hp
  have hmod := nat_grid_mod A
    (ciU A+(x+ciV A)/ciH A*ciK A-(symmetricReturnTuple A hB ell).2.2)
    ((x+ciV A)%ciH A) 0
  simp only [zero_mul,add_zero] at hmod
  have hl := (symmetricPrefixIdeal A hQ).aperyRepresentative_le
    (routingA P.M.base A.reindex) _ hp (by exact_mod_cast hmod)
  have ha : (0 : ℤ)<n0 A := by exact_mod_cast (branchA_symmetricTailData A).n0_pos
  have hsZ : ((ciU A+(x+ciV A)/ciH A*ciK A-(symmetricReturnTuple A hB ell).2.2 : ℕ) : ℤ)+
      (symmetricReturnTuple A hB ell).2.2=(ciU A+(x+ciV A)/ciH A*ciK A : ℕ) := by
    exact_mod_cast hsubx
  have hdP := S.2.2.2.2.1
  simp only [Nat.cast_add,Nat.cast_mul] at hl
  change _ < _
  nlinarith

private theorem grid_add_b (A : SectorBCriticalRoleBranchA P) (x y : ℕ) :
    gridResidue P.M.base A.reindex x y+ (routingB P.M.base A.reindex : ℕ)=
      gridResidue P.M.base A.reindex (x+1) y := by
  simp only [gridResidue,Nat.cast_add,Nat.cast_one]
  ring
private theorem grid_add_c (A : SectorBCriticalRoleBranchA P) (x y : ℕ) :
    gridResidue P.M.base A.reindex x y+ (routingC P.M.base A.reindex : ℕ)=
      gridResidue P.M.base A.reindex x (y+1) := by
  simp only [gridResidue,Nat.cast_add,Nat.cast_one]
  ring

private theorem grid_b_wrap (A : SectorBCriticalRoleBranchA P) (y : ℕ) :
    gridResidue P.M.base A.reindex (ciH A) y=gridResidue P.M.base A.reindex 0 y := by
  have hc := congrArg (fun t : ℕ => (t : ZMod (routingA P.M.base A.reindex))) (symmetric_ci_b_carry A)
  simp only [Nat.cast_mul,← routingA_eq_n0 A,← routingB_eq_n1 A,ZMod.natCast_self,mul_zero] at hc
  simp only [gridResidue,Nat.cast_zero,zero_mul,hc,zero_add]

private theorem grid_c_wrap (A : SectorBCriticalRoleBranchA P) (x : ℕ) :
    gridResidue P.M.base A.reindex x (ciG A)=
      gridResidue P.M.base A.reindex ((x+ciV A)%ciH A) 0 := by
  have hc := congrArg (fun t : ℕ => (t : ZMod (routingA P.M.base A.reindex))) (symmetric_ci_c_carry A x)
  simp only [Nat.cast_add,Nat.cast_mul,← routingA_eq_n0 A,← routingB_eq_n1 A,
    ← routingC_eq_n2 A,ZMod.natCast_self,mul_zero,add_zero] at hc
  simpa only [gridResidue,Nat.cast_zero,zero_mul,add_zero] using hc

private theorem prefix_lambda_lower (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) {x y : ℕ}
    (hx : x < ciH A) (hy : y < ciG A) :
    (x : ℤ)*n1 A+y*n2 A ≤ symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex x y) := by
  have hm := (symmetricPrefixIdeal A hQ).aperyRepresentative_mem
    (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex x y)
  obtain ⟨ell,_,_,hmem⟩ := hm
  have hl := (routingH P.M.base A.reindex).asRelativeIdeal.aperyRepresentative_le
    (routingA P.M.base A.reindex) _ hmem.1
    ((symmetricPrefixIdeal A hQ).aperyRepresentative_mod _ _)
  have hc := symmetric_ci_rectangle_canonical A hx hy
  change ((normalizedGrid P.M.base A.reindex 0 x y : ℕ) : ℤ)=
    (routingH P.M.base A.reindex).asRelativeIdeal.aperyRepresentative
      (routingA P.M.base A.reindex) _ at hc
  rw [← hc] at hl
  simpa only [normalizedGrid,zero_mul,zero_add,Nat.cast_add,Nat.cast_mul,
    routingB_eq_n1 A,routingC_eq_n2 A] using hl

private theorem prefix_F_quadrant (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ell : SymmetricReturnIndex A) {x y : ℕ}
    (hi : (symmetricReturnTuple A hB ell).1 ≤ x)
    (hj : (symmetricReturnTuple A hB ell).2.1 ≤ y) :
    ((x*n1 A+y*n2 A : ℕ) : ℤ) ∈ symmetricPrefixIdeal A hQ := by
  have S := symmetricReturnTuple_spec A hB ell
  have hm := (symmetric_single_return_sources_mem A hB ell.property.1
    S.2.1 S.2.2.2.1 S.2.2.2.2.2.2.2).1
  have hd := gridH A 0 (x-(symmetricReturnTuple A hB ell).1)
    (y-(symmetricReturnTuple A hB ell).2.1)
  obtain ⟨n,hn,hne⟩ := hd
  have hp : (symmetricF A (symmetricReturnTuple A hB ell).1
      (symmetricReturnTuple A hB ell).2.1 : ℤ)+n ∈ symmetricPrefixIdeal A hQ :=
    ⟨ell.val,ell.property.1,ell.property.2,(returnIdeal _ _).add_mem hm hn⟩
  have hxi : ((x-(symmetricReturnTuple A hB ell).1 : ℕ) : ℤ)+
    (symmetricReturnTuple A hB ell).1=x := by exact_mod_cast Nat.sub_add_cancel hi
  have hyj : ((y-(symmetricReturnTuple A hB ell).2.1 : ℕ) : ℤ)+
    (symmetricReturnTuple A hB ell).2.1=y := by exact_mod_cast Nat.sub_add_cancel hj
  simp only [symmetricF,Nat.cast_add,Nat.cast_mul,zero_mul,zero_add] at hne hp ⊢
  convert hp using 1 <;> nlinarith only [hne,hxi,hyj]

private theorem branch_step_zero (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) {r : ZMod (routingA P.M.base A.reindex)}
    (hr : (symmetricPrefixRouting A hQ).IsBranch r) :
    symmetricPrefixLambda A hQ r+routingB P.M.base A.reindex=
      symmetricPrefixLambda A hQ (r+routingB P.M.base A.reindex) ∧
    symmetricPrefixLambda A hQ r+routingC P.M.base A.reindex=
      symmetricPrefixLambda A hQ (r+routingC P.M.base A.reindex) := by
  have hb := (symmetricPrefixIdeal A hQ).apery_step_eq
    (routingA P.M.base A.reindex) (routingB P.M.base A.reindex) (routingHB _ _) r
  have hc := (symmetricPrefixIdeal A hQ).apery_step_eq
    (routingA P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHC _ _) r
  change (symmetricPrefixIdeal A hQ).aperyStepQuotient _ _ (routingHB _ _) r=0 ∧
    (symmetricPrefixIdeal A hQ).aperyStepQuotient _ _ (routingHC _ _) r=0 at hr
  rw [hr.1] at hb
  rw [hr.2] at hc
  simpa only [Nat.cast_zero,mul_zero,add_zero] using And.intro hb hc

/-- Same inverse-X diamond: the canonical c-successor and the strict
b-successor threshold exclude two zero outgoing defects. -/
theorem symmetric_prefix_inverseX_not_branch (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ell : SymmetricReturnIndex A) {r : ZMod (routingA P.M.base A.reindex)}
    (ht : (symmetricPrefixRouting A hQ).branchTarget r=
      gridResidue P.M.base A.reindex 0 (symmetricReturnTuple A hB ell).2.1) :
    ¬ (symmetricPrefixRouting A hQ).IsBranch r := by
  intro hr
  let j := (symmetricReturnTuple A hB ell).2.1
  have S := symmetricReturnTuple_spec A hB ell
  have hhP := (symmetric_ci_normalized_equations A).2.1
  have hjP := S.2.2.1
  have hj := S.2.2.2.1
  have hb : gridResidue P.M.base A.reindex (ciH A-1) (j-1)+routingB P.M.base A.reindex=
      gridResidue P.M.base A.reindex 0 (j-1) := by
    rw [grid_add_b, Nat.sub_add_cancel (by omega : 1 ≤ ciH A),grid_b_wrap]
  have hc : gridResidue P.M.base A.reindex (ciH A-1) (j-1)+routingC P.M.base A.reindex=
      gridResidue P.M.base A.reindex (ciH A-1) j := by
    rw [grid_add_c,Nat.sub_add_cancel (by omega : 1 ≤ j)]
  have he : r=gridResidue P.M.base A.reindex (ciH A-1) (j-1) := by
    have ht' : r+routingB P.M.base A.reindex+routingC P.M.base A.reindex=
        gridResidue P.M.base A.reindex 0 j := ht
    have hd : gridResidue P.M.base A.reindex (ciH A-1) (j-1)+
        routingB P.M.base A.reindex+routingC P.M.base A.reindex=
        gridResidue P.M.base A.reindex 0 j := by rw [hb,grid_add_c,Nat.sub_add_cancel (by omega : 1 ≤ j)]
    exact add_right_cancel (add_right_cancel (ht'.trans hd.symm))
  subst r
  have hs := branch_step_zero A hQ hr
  rw [hb] at hs
  rw [hc] at hs
  have hm := prefix_F_quadrant A hB hQ ell
    (by have := S.2.1; omega : (symmetricReturnTuple A hB ell).1 ≤ ciH A-1) (le_refl j)
  have hl := (symmetricPrefixIdeal A hQ).aperyRepresentative_le (routingA P.M.base A.reindex)
    _ hm (by
      have hh := nat_grid_mod A 0 (ciH A-1) j
      simp only [zero_mul,zero_add] at hh
      exact_mod_cast hh)
  have hlo := prefix_lambda_lower A hQ (by omega : ciH A-1 < ciH A) (by dsimp [j]; omega : j-1 < ciG A)
  have he0 : symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex (ciH A-1) (j-1))=
      (ciH A-1 : ℕ)* (n1 A : ℤ)+(j-1 : ℕ)*(n2 A : ℤ) := by
    rw [routingC_eq_n2 A] at hs
    simp only [Nat.cast_add,Nat.cast_mul,zero_mul,zero_add] at hl
    have hjZ : ((j-1 : ℕ) : ℤ)+1=j := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ j)
    nlinarith only [hl,hs.2,hlo,hjZ]
  have hm0 := (symmetricPrefixIdeal A hQ).aperyRepresentative_mem
    (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex (ciH A-1) (j-1))
  change symmetricPrefixLambda A hQ _ ∈ symmetricPrefixIdeal A hQ at hm0
  rw [he0] at hm0
  have hth := symmetric_prefix_inverseX_threshold A hB hQ
    (by omega : ciH A-1 < ciH A) (by dsimp [j]; omega : j-1 < ciG A)
    (by simpa only [Nat.cast_add,Nat.cast_mul] using hm0)
  rw [he0,routingB_eq_n1 A] at hs
  have hpureZ := congrArg (fun t : ℕ => (t : ℤ)) (symmetric_ci_b_carry A)
  simp only [Nat.cast_mul] at hpureZ
  have hhZ : ((ciH A-1 : ℕ) : ℤ)+1=ciH A := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ ciH A)
  nlinarith only [hs.1,hth,hpureZ,hhZ]

/-- The inverse-Y diamond uses the actual cyclic carry, including its
additional b-wrap, rather than an assumed constant top carry. -/
theorem symmetric_prefix_inverseY_not_branch (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ell : SymmetricReturnIndex A) {r : ZMod (routingA P.M.base A.reindex)}
    (ht : (symmetricPrefixRouting A hQ).branchTarget r=
      gridResidue P.M.base A.reindex
        (((symmetricReturnTuple A hB ell).1+ciV A)%ciH A) 0) :
    ¬ (symmetricPrefixRouting A hQ).IsBranch r := by
  intro hr
  let i := (symmetricReturnTuple A hB ell).1
  have S := symmetricReturnTuple_spec A hB ell
  have hgP := (symmetric_ci_normalized_equations A).1
  have hiP := S.1
  have hi := S.2.1
  have hb : gridResidue P.M.base A.reindex (i-1) (ciG A-1)+routingB P.M.base A.reindex=
      gridResidue P.M.base A.reindex i (ciG A-1) := by
    rw [grid_add_b,Nat.sub_add_cancel (by omega : 1 ≤ i)]
  have hc : gridResidue P.M.base A.reindex (i-1) (ciG A-1)+routingC P.M.base A.reindex=
      gridResidue P.M.base A.reindex (((i-1)+ciV A)%ciH A) 0 := by
    rw [grid_add_c,Nat.sub_add_cancel (by omega : 1 ≤ ciG A),grid_c_wrap]
  have he : r=gridResidue P.M.base A.reindex (i-1) (ciG A-1) := by
    have ht' : r+routingB P.M.base A.reindex+routingC P.M.base A.reindex=
        gridResidue P.M.base A.reindex ((i+ciV A)%ciH A) 0 := ht
    have hd : gridResidue P.M.base A.reindex (i-1) (ciG A-1)+
        routingB P.M.base A.reindex+routingC P.M.base A.reindex=
        gridResidue P.M.base A.reindex ((i+ciV A)%ciH A) 0 := by
      rw [hb,grid_add_c,Nat.sub_add_cancel (by omega : 1 ≤ ciG A),grid_c_wrap]
    exact add_right_cancel (add_right_cancel (ht'.trans hd.symm))
  subst r
  have hs := branch_step_zero A hQ hr
  rw [hb,hc] at hs
  have hm := prefix_F_quadrant A hB hQ ell (le_refl i)
    (by have := S.2.2.2.1; omega : (symmetricReturnTuple A hB ell).2.1 ≤ ciG A-1)
  have hl := (symmetricPrefixIdeal A hQ).aperyRepresentative_le (routingA P.M.base A.reindex)
    _ hm (by
      have hh := nat_grid_mod A 0 i (ciG A-1)
      simp only [zero_mul,zero_add] at hh
      exact_mod_cast hh)
  have hlo := prefix_lambda_lower A hQ (by dsimp [i]; omega : i-1 < ciH A)
    (by omega : ciG A-1 < ciG A)
  have he0 : symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex (i-1) (ciG A-1))=
      (i-1 : ℕ)*(n1 A : ℤ)+(ciG A-1 : ℕ)*(n2 A : ℤ) := by
    rw [routingB_eq_n1 A] at hs
    simp only [Nat.cast_add,Nat.cast_mul] at hl
    have hiZ : ((i-1 : ℕ) : ℤ)+1=i := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ i)
    nlinarith only [hl,hs.1,hlo,hiZ]
  have hm0 := (symmetricPrefixIdeal A hQ).aperyRepresentative_mem
    (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex (i-1) (ciG A-1))
  change symmetricPrefixLambda A hQ _ ∈ symmetricPrefixIdeal A hQ at hm0
  rw [he0] at hm0
  have hth := symmetric_prefix_inverseY_threshold A hB hQ
    (by dsimp [i]; omega : i-1 < ciH A) (by omega : ciG A-1 < ciG A)
    (by simpa only [Nat.cast_add,Nat.cast_mul] using hm0)
  rw [he0,routingC_eq_n2 A] at hs
  have hcarryZ : (i-1 : ℕ)*(n1 A : ℤ)+ciG A*n2 A=
      (((i-1+ciV A)%ciH A : ℕ) : ℤ)*n1 A+
        (ciU A+(i-1+ciV A)/ciH A*ciK A : ℕ)* (n0 A : ℤ) := by
    exact_mod_cast symmetric_ci_c_carry A (i-1)
  have hgZ : ((ciG A-1 : ℕ) : ℤ)+1=ciG A := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ ciG A)
  nlinarith only [hs.2,hth,hcarryZ,hgZ]

private theorem minimal_eq_divisor (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) {z g : ℤ}
    (hz : (symmetricPrefixIdeal A hQ).IsMinimalGenerator z)
    (hg : g ∈ symmetricPrefixIdeal A hQ)
    (hd : z-g ∈ (routingH P.M.base A.reindex).asRelativeIdeal) : z=g := by
  obtain ⟨n,hn,he⟩ := hd
  by_cases h : n=0
  · subst n; simp only [Nat.cast_zero] at he; omega
  · have hh := hz.2 n hn h
    apply False.elim
    apply hh
    convert hg using 1 <;> omega

/-- A genuine prefix branch-target source is an actual height-zero F-return.
The two other generators are excluded on their own inverse diamonds. -/
theorem symmetric_prefix_C_targets_F
    (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 2 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    let I := symmetricPrefixIdeal A (by omega : 1 < actualPrincipalIndex P.M.base)
    let D := symmetricPrefixRouting A (by omega : 1 < actualPrincipalIndex P.M.base)
    ∀ r, D.IsBranch r → D.IsSource (D.branchTarget r) →
      ∃ ell : SymmetricReturnIndex A,
        I.aperyRepresentative (routingA P.M.base A.reindex) (D.branchTarget r)=
        (symmetricF A (symmetricReturnTuple A hB ell).1
          (symmetricReturnTuple A hB ell).2.1 : ℤ) := by
  dsimp only
  let hQ1 : 1 < actualPrincipalIndex P.M.base := by omega
  intro r hr hs
  let z := symmetricPrefixLambda A hQ1 ((symmetricPrefixRouting A hQ1).branchTarget r)
  have hgen := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base A.reindex)).1
  have hmin : (symmetricPrefixIdeal A hQ1).IsMinimalGenerator z :=
    ((symmetricPrefixIdeal A hQ1).concrete_isSource_iff_isMinimalGenerator
      (routingA P.M.base A.reindex) (routingB P.M.base A.reindex)
      (routingC P.M.base A.reindex) hgen (routingHB _ _) (routingHC _ _)
      (by rw [routingB_eq_n1 A]; exact (branchA_symmetricTailData A).n1_pos.ne')
      (by rw [routingC_eq_n2 A]; exact (branchA_symmetricTailData A).n2_pos.ne') _).mp hs
  obtain ⟨l,hl,hlt,hmem⟩ := hmin.1
  let ell : SymmetricReturnIndex A := ⟨l,hl,hlt⟩
  have S := symmetricReturnTuple_spec A hB ell
  have hg := symmetric_single_return_sources_mem A hB hl S.2.1 S.2.2.2.1 S.2.2.2.2.2.2.2
  have hF : (symmetricF A (symmetricReturnTuple A hB ell).1
      (symmetricReturnTuple A hB ell).2.1 : ℤ) ∈ symmetricPrefixIdeal A hQ1 := ⟨l,hl,hlt,hg.1⟩
  have hX : (symmetricX A (symmetricReturnTuple A hB ell).2.1
      (symmetricReturnTuple A hB ell).2.2 : ℤ) ∈ symmetricPrefixIdeal A hQ1 := ⟨l,hl,hlt,hg.2.1⟩
  have hY : (symmetricY A (symmetricReturnTuple A hB ell).1
      (symmetricReturnTuple A hB ell).2.2 : ℤ) ∈ symmetricPrefixIdeal A hQ1 := ⟨l,hl,hlt,hg.2.2⟩
  rcases (symmetric_single_return_three_sources A hB hl S.2.1 S.2.2.2.1
    S.2.2.2.2.2.2.2 z).mp hmem with hd | hd | hd
  · exact ⟨ell,minimal_eq_divisor A hQ1 hmin hF hd⟩
  · have he := minimal_eq_divisor A hQ1 hmin hX hd
    have hmod := (symmetricPrefixIdeal A hQ1).aperyRepresentative_mod
      (routingA P.M.base A.reindex) ((symmetricPrefixRouting A hQ1).branchTarget r)
    change (z : ZMod (routingA P.M.base A.reindex))=_ at hmod
    rw [he] at hmod
    have hgmod := nat_grid_mod A (ciK A-(symmetricReturnTuple A hB ell).2.2)
      0 (symmetricReturnTuple A hB ell).2.1
    simp only [zero_mul,add_zero] at hgmod
    have ht : (symmetricPrefixRouting A hQ1).branchTarget r=
        gridResidue P.M.base A.reindex 0 (symmetricReturnTuple A hB ell).2.1 := by
      rw [← hmod]; exact_mod_cast hgmod
    exact False.elim (symmetric_prefix_inverseX_not_branch A hB hQ1 ell ht hr)
  · have he := minimal_eq_divisor A hQ1 hmin hY hd
    have hmod := (symmetricPrefixIdeal A hQ1).aperyRepresentative_mod
      (routingA P.M.base A.reindex) ((symmetricPrefixRouting A hQ1).branchTarget r)
    change (z : ZMod (routingA P.M.base A.reindex))=_ at hmod
    rw [he] at hmod
    have hgmod := nat_grid_mod A
      (ciU A+((symmetricReturnTuple A hB ell).1+ciV A)/ciH A*ciK A-
        (symmetricReturnTuple A hB ell).2.2)
      (((symmetricReturnTuple A hB ell).1+ciV A)%ciH A) 0
    simp only [zero_mul,add_zero] at hgmod
    have ht : (symmetricPrefixRouting A hQ1).branchTarget r=
        gridResidue P.M.base A.reindex (((symmetricReturnTuple A hB ell).1+ciV A)%ciH A) 0 := by
      rw [← hmod]; exact_mod_cast hgmod
    exact False.elim (symmetric_prefix_inverseY_not_branch A hB hQ1 ell ht hr)

/-- The actual zero-height prefix region is precisely the union of the
northeast F-quadrants, independent of any choice of minimal return list. -/
theorem symmetric_prefix_height_zero_iff_F_quadrant (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    {x y : ℕ} (hx : x < ciH A) (hy : y < ciG A) :
    symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex x y)=
      (x*n1 A+y*n2 A : ℕ) ↔
    ∃ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).1 ≤ x ∧
      (symmetricReturnTuple A hB ell).2.1 ≤ y := by
  constructor
  · intro he
    have hm := (symmetricPrefixIdeal A hQ).aperyRepresentative_mem
      (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex x y)
    change symmetricPrefixLambda A hQ _ ∈ symmetricPrefixIdeal A hQ at hm
    rw [he] at hm
    exact canonical_prefix_coords A hB hx hy hm
  · rintro ⟨ell,hi,hj⟩
    have hm := prefix_F_quadrant A hB hQ ell hi hj
    have hh := nat_grid_mod A 0 x y
    simp only [zero_mul,zero_add] at hh
    have hl := (symmetricPrefixIdeal A hQ).aperyRepresentative_le
      (routingA P.M.base A.reindex) _ hm (by exact_mod_cast hh)
    have hlo := prefix_lambda_lower A hQ hx hy
    simp only [Nat.cast_add,Nat.cast_mul] at hl ⊢
    exact le_antisymm hl hlo

/-- The extra corner itself has height zero. Outgoing carries and its
resource tags are separate statements, not built into this theorem. -/
theorem symmetric_prefix_kappa_height_zero (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex (ciH A-1) (ciG A-1))=
      ((ciH A-1)*n1 A+(ciG A-1)*n2 A : ℕ) := by
  have hhP := (symmetric_ci_normalized_equations A).2.1
  have hgP := (symmetric_ci_normalized_equations A).1
  apply (symmetric_prefix_height_zero_iff_F_quadrant A hB hQ (by omega) (by omega)).mpr
  let ell : SymmetricReturnIndex A := ⟨1,by omega,by omega⟩
  have S := symmetricReturnTuple_spec A hB ell
  exact ⟨ell,by have := S.2.1; omega,by have := S.2.2.2.1; omega⟩

private theorem prefix_b_step (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (r : ZMod (routingA P.M.base A.reindex)) :
    symmetricPrefixLambda A hQ r+routingB P.M.base A.reindex=
      symmetricPrefixLambda A hQ (r+routingB P.M.base A.reindex)+
        routingA P.M.base A.reindex*(symmetricPrefixRouting A hQ).u r := by
  exact (symmetricPrefixIdeal A hQ).apery_step_eq _ _ (routingHB _ _) r
private theorem prefix_c_step (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (r : ZMod (routingA P.M.base A.reindex)) :
    symmetricPrefixLambda A hQ r+routingC P.M.base A.reindex=
      symmetricPrefixLambda A hQ (r+routingC P.M.base A.reindex)+
        routingA P.M.base A.reindex*(symmetricPrefixRouting A hQ).v r := by
  exact (symmetricPrefixIdeal A hQ).apery_step_eq _ _ (routingHC _ _) r

/-- Source-coordinate conditions of an ordinary staircase notch give the
actual unused-merge resource. No graph incidence is assumed in the input. -/
theorem symmetric_prefix_ordinary_notch_unused (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    {x y : ℕ} (hx : x+1 < ciH A) (hy : y+1 < ciG A)
    (hsw : ∀ ell : SymmetricReturnIndex A,
      ¬ ((symmetricReturnTuple A hB ell).1 ≤ x ∧ (symmetricReturnTuple A hB ell).2.1 ≤ y))
    (hse : ∃ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).1 ≤ x+1 ∧ (symmetricReturnTuple A hB ell).2.1 ≤ y)
    (hnw : ∃ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).1 ≤ x ∧ (symmetricReturnTuple A hB ell).2.1 ≤ y+1) :
    L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (symmetricPrefixRouting A hQ)
      (gridResidue P.M.base A.reindex x y) := by
  have hse0 := (symmetric_prefix_height_zero_iff_F_quadrant A hB hQ hx (by omega)).mpr hse
  have hnw0 := (symmetric_prefix_height_zero_iff_F_quadrant A hB hQ (by omega) hy).mpr hnw
  have hne0 := (symmetric_prefix_height_zero_iff_F_quadrant A hB hQ hx hy).mpr
    (by obtain ⟨ell,hi,hj⟩ := hse; exact ⟨ell,hi,by omega⟩)
  have hsw0 : symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex x y) ≠
      (x*n1 A+y*n2 A : ℕ) := by
    intro he
    obtain ⟨ell,he⟩ := (symmetric_prefix_height_zero_iff_F_quadrant A hB hQ (by omega) (by omega)).mp he
    exact hsw ell he
  have hlo := prefix_lambda_lower A hQ (by omega : x < ciH A) (by omega : y < ciG A)
  have hb := prefix_b_step A hQ (gridResidue P.M.base A.reindex x y)
  have hc := prefix_c_step A hQ (gridResidue P.M.base A.reindex x y)
  have hbc := prefix_b_step A hQ (gridResidue P.M.base A.reindex x (y+1))
  have hcb := prefix_c_step A hQ (gridResidue P.M.base A.reindex (x+1) y)
  rw [grid_add_b,hse0,routingB_eq_n1 A] at hb
  rw [grid_add_c,hnw0,routingC_eq_n2 A] at hc
  rw [grid_add_b,hne0,hnw0,routingB_eq_n1 A] at hbc
  rw [grid_add_c,hne0,hse0,routingC_eq_n2 A] at hcb
  have ha : (0 : ℤ)<routingA P.M.base A.reindex := by exact_mod_cast routingA_pos P.M.base A.reindex
  have hup : 0 < (symmetricPrefixRouting A hQ).u (gridResidue P.M.base A.reindex x y) := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hsw0
    rw [hz] at hb
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_zero,mul_zero,add_zero] at hb ⊢
    nlinarith only [hb]
  have huv : (symmetricPrefixRouting A hQ).u (gridResidue P.M.base A.reindex x y)=
      (symmetricPrefixRouting A hQ).v (gridResidue P.M.base A.reindex x y) := by
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hb hc
    have he : ((symmetricPrefixRouting A hQ).u (gridResidue P.M.base A.reindex x y) : ℤ)=
        ((symmetricPrefixRouting A hQ).v (gridResidue P.M.base A.reindex x y) : ℤ) := by nlinarith only [hb,hc,ha]
    exact_mod_cast he
  refine ⟨huv,hup,?_,?_⟩
  · change (symmetricPrefixRouting A hQ).u (gridResidue P.M.base A.reindex x y+routingC P.M.base A.reindex)=0
    rw [grid_add_c]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hbc
    have he : ((symmetricPrefixRouting A hQ).u (gridResidue P.M.base A.reindex x (y+1)) : ℤ)=0 := by nlinarith only [hbc,ha]
    exact_mod_cast he
  · change (symmetricPrefixRouting A hQ).v (gridResidue P.M.base A.reindex x y+routingB P.M.base A.reindex)=0
    rw [grid_add_b]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hcb
    have he : ((symmetricPrefixRouting A hQ).v (gridResidue P.M.base A.reindex (x+1) y) : ℤ)=0 := by nlinarith only [hcb,ha]
    exact_mod_cast he

/-- Both actual outgoing corner defects are positive, via the same inverse
thresholds used in S2; no maximum-depth envelope is assumed. -/
theorem symmetric_prefix_kappa_isSink (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    (symmetricPrefixRouting A hQ).IsSink
      (gridResidue P.M.base A.reindex (ciH A-1) (ciG A-1)) := by
  have hhP := (symmetric_ci_normalized_equations A).2.1
  have hgP := (symmetric_ci_normalized_equations A).1
  have he := symmetric_prefix_kappa_height_zero A hB hQ
  have hm := (symmetricPrefixIdeal A hQ).aperyRepresentative_mem
    (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex (ciH A-1) (ciG A-1))
  change symmetricPrefixLambda A hQ _ ∈ symmetricPrefixIdeal A hQ at hm
  rw [he] at hm
  have hX := symmetric_prefix_inverseX_threshold A hB hQ (by omega) (by omega) hm
  have hY := symmetric_prefix_inverseY_threshold A hB hQ (by omega) (by omega) hm
  have hb := prefix_b_step A hQ (gridResidue P.M.base A.reindex (ciH A-1) (ciG A-1))
  have hc := prefix_c_step A hQ (gridResidue P.M.base A.reindex (ciH A-1) (ciG A-1))
  rw [he,grid_add_b,Nat.sub_add_cancel (by omega : 1 ≤ ciH A),grid_b_wrap,routingB_eq_n1 A] at hb
  rw [he,grid_add_c,Nat.sub_add_cancel (by omega : 1 ≤ ciG A),grid_c_wrap,routingC_eq_n2 A] at hc
  have hhb : ((ciH A-1 : ℕ) : ℤ)+1=ciH A := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ ciH A)
  have hhg : ((ciG A-1 : ℕ) : ℤ)+1=ciG A := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ ciG A)
  have hcarryB : (ciH A : ℤ)*n1 A=ciK A*n0 A := by exact_mod_cast symmetric_ci_b_carry A
  have hcarryC : (ciH A-1 : ℕ)*(n1 A : ℤ)+ciG A*n2 A=
      (((ciH A-1+ciV A)%ciH A : ℕ) : ℤ)*n1 A+
        (ciU A+(ciH A-1+ciV A)/ciH A*ciK A : ℕ)*(n0 A : ℤ) := by
    exact_mod_cast symmetric_ci_c_carry A (ciH A-1)
  change _ ≠ 0 ∧ _ ≠ 0
  constructor
  · intro hz
    rw [hz] at hb
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_zero,mul_zero,add_zero] at hb
    nlinarith only [hb,hX,hhb,hcarryB]
  · intro hz
    rw [hz] at hc
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_zero,mul_zero,add_zero] at hc
    nlinarith only [hc,hY,hhg,hcarryC]

/-- The S3 corner has a genuine fake-seat tag. This does not identify it
with an exceptional endpoint or with an unused-merge tag. -/
def symmetric_prefix_kappa_fakeSeat (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    FakeSink (symmetricPrefixIdeal A hQ) (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
      (routingHB _ _) (routingHC _ _) := by
  refine ⟨gridResidue P.M.base A.reindex (ciH A-1) (ciG A-1),
    symmetric_prefix_kappa_isSink A hB hQ,?_⟩
  change symmetricPrefixLambda A hQ _-routingA P.M.base A.reindex ∉ _
  rw [symmetric_prefix_kappa_height_zero A hB hQ,routingA_eq_n0 A]
  exact canonical_no_a A (by have := (symmetric_ci_normalized_equations A).2.1; omega)
    (by have := (symmetric_ci_normalized_equations A).1; omega)

end NS25Lean.L5A2BFinalRepair
