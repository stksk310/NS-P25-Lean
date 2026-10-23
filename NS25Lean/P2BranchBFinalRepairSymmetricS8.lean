import NS25Lean.P2BranchBFinalRepairSymmetricS2

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open FourGeneratedBridge ChosenBase L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR4R2A L5A2B4AR5A L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4C
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- A genuine maximum-depth return, selected by minimizing its positive
complementary b-carry. No finite enumeration or uniqueness is used. -/
theorem symmetric_return_depth_maximum (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    ∃ ellMax : SymmetricReturnIndex A, ∀ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).2.2 ≤ (symmetricReturnTuple A hB ellMax).2.2 := by
  let f := fun ell : SymmetricReturnIndex A => ciK A-(symmetricReturnTuple A hB ell).2.2
  obtain ⟨ellMax,he⟩ := natMinImage_spec (symmetricReturnNonempty A hQ) f
  refine ⟨ellMax,fun ell => ?_⟩
  have hm := natMinImage_le (symmetricReturnNonempty A hQ) f ell
  rw [← he] at hm
  have hd := (symmetricReturnTuple_spec A hB ell).2.2.2.2.2.1
  have hD := (symmetricReturnTuple_spec A hB ellMax).2.2.2.2.2.1
  dsimp [f] at hm
  omega

private theorem mixed_carry (A : SectorBCriticalRoleBranchA P) :
    ciG A*n2 A=ciU A*n0 A+ciV A*n1 A := by
  have S := symmetric_ci_normalized_equations A
  rw [S.2.2.2.2.2.2.1,S.2.2.2.2.2.2.2.1,S.2.2.2.2.2.2.2.2]
  ring

private theorem total_wrap_value (A : SectorBCriticalRoleBranchA P) (p q t : ℕ) :
    let Nc := t/ciG A
    let Nb := (q+Nc*ciV A)/ciH A
    p*n0 A+q*n1 A+t*n2 A=
      (p+Nc*ciU A+Nb*ciK A)*n0 A+
        ((q+Nc*ciV A)%ciH A)*n1 A+(t%ciG A)*n2 A := by
  dsimp only
  have hc := mixed_carry A
  have hb := symmetric_ci_b_carry A
  calc
    _ = p*n0 A+q*n1 A+(t%ciG A+ciG A*(t/ciG A))*n2 A := by rw [Nat.mod_add_div]
    _ = (p+t/ciG A*ciU A)*n0 A+(q+t/ciG A*ciV A)*n1 A+(t%ciG A)*n2 A := by
      calc
        _ = p*n0 A+q*n1 A+(t%ciG A)*n2 A+(t/ciG A)*(ciG A*n2 A) := by ring
        _ = _ := by rw [hc]; ring
    _ = (p+t/ciG A*ciU A)*n0 A+
        ((q+t/ciG A*ciV A)%ciH A+ciH A*((q+t/ciG A*ciV A)/ciH A))*n1 A+
        (t%ciG A)*n2 A := by rw [Nat.mod_add_div]
    _ = _ := by
      calc
        _ = (p+t/ciG A*ciU A)*n0 A+((q+t/ciG A*ciV A)%ciH A)*n1 A+
          ((q+t/ciG A*ciV A)/ciH A)*(ciH A*n1 A)+(t%ciG A)*n2 A := by ring
        _ = _ := by rw [hb]; ring

private theorem nat_grid_mod (A : SectorBCriticalRoleBranchA P) (l x y : ℕ) :
    ((l*n0 A+x*n1 A+y*n2 A : ℕ) : ZMod (routingA P.M.base A.reindex))=
      gridResidue P.M.base A.reindex x y := by
  simpa only [normalizedGrid,routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A]
    using normalizedGrid_mod P.M.base A.reindex l x y

/-- Every actual prefix representative has a total-wrap decomposition
from an actual return and a nonnegative returned H-factorization. -/
theorem symmetric_prefix_total_wrap_decomposition (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    {x y : ℕ} (hx : x < ciH A) (hy : y < ciG A) :
    ∃ (ell : SymmetricReturnIndex A) (p q t Nc Nb : ℕ),
      (symmetricReturnTuple A hB ell).2.1+t=y+ciG A*Nc ∧
      (symmetricReturnTuple A hB ell).1+q+Nc*ciV A=x+ciH A*Nb ∧
      symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex x y)+
          (symmetricReturnTuple A hB ell).2.2*n0 A=
        ((p+Nc*ciU A+Nb*ciK A : ℕ) : ℤ)*n0 A+x*n1 A+y*n2 A := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  let z := symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex x y)
  obtain ⟨l,hl,hlt,hmem⟩ := (symmetricPrefixIdeal A hQ).aperyRepresentative_mem
    (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex x y)
  let ell : SymmetricReturnIndex A := ⟨l,hl,hlt⟩
  have S := symmetricReturnTuple_spec A hB ell
  obtain ⟨w,hw,he⟩ := hmem.2
  obtain ⟨p,q,t,_,_,hf⟩ := branchA_routingH_rectangle_factorization A hw
  rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A] at hf
  let i := (symmetricReturnTuple A hB ell).1
  let j := (symmetricReturnTuple A hB ell).2.1
  let d := (symmetricReturnTuple A hB ell).2.2
  let Nc := (j+t)/ciG A
  let Nb := (i+q+Nc*ciV A)/ciH A
  let xx := (i+q+Nc*ciV A)%ciH A
  let yy := (j+t)%ciG A
  have hbal : z+(d : ℤ)*n0 A=
      (p*n0 A+(i+q)*n1 A+(j+t)*n2 A : ℕ) := by
    have hr : (i : ℤ)*n1 A+j*n2 A=(l*normalizedM P.M.base : ℕ)+(d : ℤ)*n0 A := by
      exact_mod_cast S.2.2.2.2.2.2.2
    rw [hf] at he
    change z-(l*normalizedM P.M.base : ℕ)=_ at he
    simp only [Nat.cast_add,Nat.cast_mul] at he hr ⊢
    nlinarith only [he,hr]
  have hn := total_wrap_value A p (i+q) (j+t)
  change _=(p+Nc*ciU A+Nb*ciK A)*n0 A+xx*n1 A+yy*n2 A at hn
  rw [hn] at hbal
  have hm := (symmetricPrefixIdeal A hQ).aperyRepresentative_mod
    (routingA P.M.base A.reindex) (gridResidue P.M.base A.reindex x y)
  change (z : ZMod (routingA P.M.base A.reindex))=_ at hm
  have hmod : gridResidue P.M.base A.reindex xx yy=gridResidue P.M.base A.reindex x y := by
    have hc := congrArg (fun n : ℤ => (n : ZMod (routingA P.M.base A.reindex))) hbal
    have hnmod := nat_grid_mod A (p+Nc*ciU A+Nb*ciK A) xx yy
    have hz : (((d : ℤ)*n0 A : ℤ) : ZMod (routingA P.M.base A.reindex))=0 := by
      simp only [Int.cast_mul,Int.cast_natCast,← routingA_eq_n0 A,ZMod.natCast_self,mul_zero]
    rw [Int.cast_add,hz,add_zero,hm] at hc
    exact hnmod.symm.trans (by exact_mod_cast hc.symm)
  have hrect : xx=x ∧ yy=y := by
    apply branchA_rectangle_modEq_unique A
      (Nat.mod_lt _ (symmetric_ci_normalized_equations A).2.1)
      (Nat.mod_lt _ (symmetric_ci_normalized_equations A).1) hx hy
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [gridResidue,Nat.cast_add,Nat.cast_mul] using hmod
  refine ⟨ell,p,q,t,Nc,Nb,?_,?_,?_⟩
  · have hh := Nat.mod_add_div (j+t) (ciG A)
    change yy+ciG A*Nc=j+t at hh
    omega
  · have hh := Nat.mod_add_div (i+q+Nc*ciV A) (ciH A)
    change xx+ciH A*Nb=i+q+Nc*ciV A at hh
    omega
  · rw [hrect.1,hrect.2] at hbal
    simpa only [Nat.cast_add,Nat.cast_mul] using hbal

/-- The lower half of the S8 b-corner envelope comes from an arbitrary
actual prefix return factorization and at least one b-wrap. -/
theorem symmetric_prefix_corner_b_height_lower (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ellMax : SymmetricReturnIndex A)
    (hmax : ∀ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).2.2 ≤ (symmetricReturnTuple A hB ellMax).2.2) :
    ((ciK A-(symmetricReturnTuple A hB ellMax).2.2)*n0 A+(ciG A-1)*n2 A : ℕ) ≤
      symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex 0 (ciG A-1)) := by
  have hh := (symmetric_ci_normalized_equations A).2.1
  have hg := (symmetric_ci_normalized_equations A).1
  obtain ⟨ell,p,q,t,Nc,Nb,hc,hb,he⟩ :=
    symmetric_prefix_total_wrap_decomposition A hB hQ (x := 0) (y := ciG A-1)
      (by omega) (by omega)
  have hi := (symmetricReturnTuple_spec A hB ell).1
  have hNb : 1 ≤ Nb := by
    by_contra hz
    have hn : Nb=0 := by omega
    rw [hn,mul_zero] at hb
    omega
  have hd := hmax ell
  have hD := (symmetricReturnTuple_spec A hB ellMax).2.2.2.2.2.1
  have hs : ((ciK A-(symmetricReturnTuple A hB ellMax).2.2 : ℕ) : ℤ)+
      (symmetricReturnTuple A hB ellMax).2.2=ciK A := by
    exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hD)
  have hcost : ciK A ≤ p+Nc*ciU A+Nb*ciK A := by
    have hm := Nat.mul_le_mul_right (ciK A) hNb
    simpa only [one_mul] using hm.trans (Nat.le_add_left _ _)
  have ha : (0 : ℤ)<n0 A := by exact_mod_cast (branchA_symmetricTailData A).n0_pos
  simp only [Nat.cast_add,Nat.cast_mul,zero_mul,add_zero] at he ⊢
  have hcostZ : (ciK A : ℤ)≤(p+Nc*ciU A+Nb*ciK A : ℕ) := by exact_mod_cast hcost
  simp only [Nat.cast_add,Nat.cast_mul] at hcostZ
  have hdZ : ((symmetricReturnTuple A hB ell).2.2 : ℤ)≤(symmetricReturnTuple A hB ellMax).2.2 := by exact_mod_cast hd
  nlinarith only [he,hs,hcostZ,hdZ,ha]

private theorem gridH (A : SectorBCriticalRoleBranchA P) (p q t : ℕ) :
    ((p*n0 A+q*n1 A+t*n2 A : ℕ) : ℤ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal := by
  refine ⟨_,?_,rfl⟩
  change _ ∈ generatedThree (routingA P.M.base A.reindex)
    (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
  rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A]
  exact (mem_generatedThree_iff _ _ _ _).mpr ⟨p,q,t,rfl⟩

private theorem prefix_upper (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) {l x y : ℕ}
    (hm : ((l*n0 A+x*n1 A+y*n2 A : ℕ) : ℤ) ∈ symmetricPrefixIdeal A hQ) :
    symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex x y)≤
      (l*n0 A+x*n1 A+y*n2 A : ℕ) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  exact (symmetricPrefixIdeal A hQ).aperyRepresentative_le _ _ hm
    (by exact_mod_cast nat_grid_mod A l x y)

theorem symmetric_prefix_corner_b_height_exact (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ellMax : SymmetricReturnIndex A)
    (hmax : ∀ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).2.2 ≤ (symmetricReturnTuple A hB ellMax).2.2) :
    symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex 0 (ciG A-1))=
      ((ciK A-(symmetricReturnTuple A hB ellMax).2.2)*n0 A+(ciG A-1)*n2 A : ℕ) := by
  apply le_antisymm _ (symmetric_prefix_corner_b_height_lower A hB hQ ellMax hmax)
  have S := symmetricReturnTuple_spec A hB ellMax
  have hm := (symmetric_single_return_sources_mem A hB ellMax.property.1
    S.2.1 S.2.2.2.1 S.2.2.2.2.2.2.2).2.1
  let j := (symmetricReturnTuple A hB ellMax).2.1
  let d := (symmetricReturnTuple A hB ellMax).2.2
  have hj : j ≤ ciG A-1 := by have := S.2.2.2.1; omega
  obtain ⟨v,hv,he⟩ := gridH A 0 0 (ciG A-1-j)
  have hp : (symmetricX A j d : ℤ)+v ∈ symmetricPrefixIdeal A hQ :=
    ⟨ellMax.val,ellMax.property.1,ellMax.property.2,(returnIdeal _ _).add_mem hm hv⟩
  have hjZ : ((ciG A-1-j : ℕ) : ℤ)+j=(ciG A-1 : ℕ) := by
    exact_mod_cast Nat.sub_add_cancel hj
  have heq : (symmetricX A j d : ℤ)+v=
      ((ciK A-d)*n0 A+0*n1 A+(ciG A-1)*n2 A : ℕ) := by
    simp only [symmetricX,zero_mul,zero_add,Nat.cast_add,Nat.cast_mul,Nat.cast_zero,add_zero] at he ⊢
    nlinarith only [he,hjZ]
  rw [heq] at hp
  simpa only [zero_mul,add_zero] using prefix_upper A hQ hp

private theorem cyclic_upper (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ell : SymmetricReturnIndex A) {x Nb : ℕ}
    (hb : (symmetricReturnTuple A hB ell).1+ciV A ≤ x+ciH A*Nb)
    (hd : (symmetricReturnTuple A hB ell).2.2 ≤ ciU A+Nb*ciK A) :
    symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex x 0) ≤
      ((ciU A+Nb*ciK A-(symmetricReturnTuple A hB ell).2.2)*n0 A+x*n1 A : ℕ) := by
  let i := (symmetricReturnTuple A hB ell).1
  let j := (symmetricReturnTuple A hB ell).2.1
  let d := (symmetricReturnTuple A hB ell).2.2
  have S := symmetricReturnTuple_spec A hB ell
  have hbZ : ((x+ciH A*Nb-(i+ciV A) : ℕ) : ℤ)+(i+ciV A : ℕ)=(x+ciH A*Nb : ℕ) := by
    exact_mod_cast Nat.sub_add_cancel hb
  have hjZ : ((ciG A-j : ℕ) : ℤ)+j=ciG A := by
    exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt S.2.2.2.1)
  have hdZ : ((ciU A+Nb*ciK A-d : ℕ) : ℤ)+d=(ciU A+Nb*ciK A : ℕ) := by
    exact_mod_cast Nat.sub_add_cancel hd
  have hbal : (i : ℤ)*n1 A+j*n2 A=(ell.val*normalizedM P.M.base : ℕ)+(d : ℤ)*n0 A := by
    exact_mod_cast S.2.2.2.2.2.2.2
  have hc : (ciG A : ℤ)*n2 A=ciU A*n0 A+ciV A*n1 A := by exact_mod_cast mixed_carry A
  have hp : (ciH A : ℤ)*n1 A=ciK A*n0 A := by exact_mod_cast symmetric_ci_b_carry A
  have hpn := congrArg (fun v : ℤ => (Nb : ℤ)*v) hp
  have he : (((ciU A+Nb*ciK A-d)*n0 A+x*n1 A : ℕ) : ℤ)-(ell.val*normalizedM P.M.base : ℕ)=
      ((x+ciH A*Nb-(i+ciV A))*n1 A+(ciG A-j)*n2 A : ℕ) := by
    simp only [Nat.cast_add,Nat.cast_mul] at hbZ hdZ hbal hc ⊢
    nlinarith only [hbZ,hjZ,hdZ,hbal,hc,hpn]
  have hm : (((ciU A+Nb*ciK A-d)*n0 A+x*n1 A : ℕ) : ℤ) ∈ symmetricPrefixIdeal A hQ := by
    refine ⟨ell.val,ell.property.1,ell.property.2,?_,?_⟩
    · simpa only [zero_mul,add_zero] using gridH A (ciU A+Nb*ciK A-d) x 0
    · change (((ciU A+Nb*ciK A-d)*n0 A+x*n1 A : ℕ) : ℤ)-
        (ell.val*normalizedM P.M.base : ℕ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal
      rw [he]
      simpa only [zero_mul,zero_add] using gridH A 0 (x+ciH A*Nb-(i+ciV A)) (ciG A-j)
  simpa only [zero_mul,add_zero] using prefix_upper A hQ (y := 0) (by simpa using hm)

private theorem cyclic_lower (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ellMax : SymmetricReturnIndex A)
    (hmax : ∀ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).2.2 ≤ (symmetricReturnTuple A hB ellMax).2.2)
    {x bmin : ℕ} (hx : x < ciH A) (hbm : bmin ≤ 1)
    (hforce : 0 < bmin → x ≤ ciV A)
    (hD : (symmetricReturnTuple A hB ellMax).2.2 ≤ ciU A+bmin*ciK A) :
    ((ciU A+bmin*ciK A-(symmetricReturnTuple A hB ellMax).2.2)*n0 A+x*n1 A : ℕ) ≤
      symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex x 0) := by
  have hg := (symmetric_ci_normalized_equations A).1
  obtain ⟨ell,p,q,t,Nc,Nb,hc,hb,he⟩ :=
    symmetric_prefix_total_wrap_decomposition A hB hQ (x := x) (y := 0) hx (by omega)
  have S := symmetricReturnTuple_spec A hB ell
  have hNc : 1 ≤ Nc := by
    by_contra hn
    have hz : Nc=0 := by omega
    rw [hz,mul_zero] at hc
    have := S.2.2.1
    omega
  have hNb : bmin ≤ Nb := by
    by_cases hm : bmin=0
    · omega
    have hxv := hforce (by omega)
    have hmul := Nat.mul_le_mul_right (ciV A) hNc
    simp only [one_mul] at hmul
    by_contra hn
    have hz : Nb=0 := by omega
    rw [hz,mul_zero] at hb
    have := S.1
    omega
  have hcost : ciU A+bmin*ciK A ≤ p+Nc*ciU A+Nb*ciK A := by
    have hmC := Nat.mul_le_mul_right (ciU A) hNc
    have hmB := Nat.mul_le_mul_right (ciK A) hNb
    simp only [one_mul] at hmC
    omega
  have hs : ((ciU A+bmin*ciK A-(symmetricReturnTuple A hB ellMax).2.2 : ℕ) : ℤ)+
      (symmetricReturnTuple A hB ellMax).2.2=(ciU A+bmin*ciK A : ℕ) := by
    exact_mod_cast Nat.sub_add_cancel hD
  have hd := hmax ell
  have ha : (0 : ℤ)<n0 A := by exact_mod_cast (branchA_symmetricTailData A).n0_pos
  have hcostZ : ((ciU A+bmin*ciK A : ℕ) : ℤ)≤(p+Nc*ciU A+Nb*ciK A : ℕ) := by exact_mod_cast hcost
  have hdZ : ((symmetricReturnTuple A hB ell).2.2 : ℤ)≤(symmetricReturnTuple A hB ellMax).2.2 := by exact_mod_cast hd
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_zero,zero_mul,add_zero] at he hs hcostZ ⊢
  have hmC := mul_le_mul_of_nonneg_right hcostZ (le_of_lt ha)
  have hmD := mul_le_mul_of_nonneg_right hdZ (le_of_lt ha)
  nlinarith only [he,hs,hmC,hmD]

theorem symmetric_prefix_corner_c_height_exact_of_pos (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ellMax : SymmetricReturnIndex A)
    (hmax : ∀ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).2.2 ≤ (symmetricReturnTuple A hB ellMax).2.2)
    (hV : 0 < ciV A) {x : ℕ} (hxlo : ciV A-1 ≤ x) (hxhi : x ≤ ciV A) :
    symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex x 0)=
      ((ciU A+ciK A-(symmetricReturnTuple A hB ellMax).2.2)*n0 A+x*n1 A : ℕ) := by
  have hvh := (symmetric_ci_normalized_equations A).2.2.2.1
  have S := symmetricReturnTuple_spec A hB ellMax
  have hd : (symmetricReturnTuple A hB ellMax).2.2 ≤ ciU A+1*ciK A := by
    have := S.2.2.2.2.2.1
    omega
  have hlo := cyclic_lower A hB hQ ellMax hmax (x := x) (bmin := 1)
    (by omega) (by omega) (fun _ => hxhi) hd
  have hup := cyclic_upper A hB hQ ellMax (x := x) (Nb := 1) (by
    have := S.2.1
    omega) hd
  simpa only [one_mul] using le_antisymm hup hlo

theorem symmetric_prefix_corner_c_height_exact_of_zero (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ellMax : SymmetricReturnIndex A)
    (hmax : ∀ ell : SymmetricReturnIndex A,
      (symmetricReturnTuple A hB ell).2.2 ≤ (symmetricReturnTuple A hB ellMax).2.2)
    (hV : ciV A=0) :
    symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex (ciH A-1) 0)=
      ((ciU A-(symmetricReturnTuple A hB ellMax).2.2)*n0 A+(ciH A-1)*n1 A : ℕ) ∧
    symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex 0 0)=
      ((ciU A+ciK A-(symmetricReturnTuple A hB ellMax).2.2)*n0 A : ℕ) := by
  have hh := (symmetric_ci_normalized_equations A).2.1
  have S := symmetricReturnTuple_spec A hB ellMax
  have hdU : (symmetricReturnTuple A hB ellMax).2.2 < ciU A := by
    have hd := S.2.2.2.2.2.2.1
    simpa only [hV,add_zero,Nat.div_eq_of_lt S.2.1,zero_mul,add_zero] using hd
  constructor
  · have hd : (symmetricReturnTuple A hB ellMax).2.2 ≤ ciU A+0*ciK A := by omega
    have hlo := cyclic_lower A hB hQ ellMax hmax (x := ciH A-1) (bmin := 0)
      (by omega) (by omega) (by omega) hd
    have hup := cyclic_upper A hB hQ ellMax (x := ciH A-1) (Nb := 0) (by
      have := S.2.1
      omega) hd
    simpa only [zero_mul,add_zero] using le_antisymm hup hlo
  · have hd : (symmetricReturnTuple A hB ellMax).2.2 ≤ ciU A+1*ciK A := by omega
    have hlo := cyclic_lower A hB hQ ellMax hmax (x := 0) (bmin := 1)
      hh (by omega) (by omega) hd
    have hup := cyclic_upper A hB hQ ellMax (x := 0) (Nb := 1) (by
      have := S.2.1
      omega) hd
    simpa only [one_mul,zero_mul,add_zero] using le_antisymm hup hlo

private theorem grid_add_b (A : SectorBCriticalRoleBranchA P) (x y : ℕ) :
    gridResidue P.M.base A.reindex x y+(routingB P.M.base A.reindex : ℕ)=
      gridResidue P.M.base A.reindex (x+1) y := by
  simp only [gridResidue,Nat.cast_add,Nat.cast_one]
  ring
private theorem grid_add_c (A : SectorBCriticalRoleBranchA P) (x y : ℕ) :
    gridResidue P.M.base A.reindex x y+(routingC P.M.base A.reindex : ℕ)=
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
private theorem prefix_b_step (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (r : ZMod (routingA P.M.base A.reindex)) :
    symmetricPrefixLambda A hQ r+routingB P.M.base A.reindex=
      symmetricPrefixLambda A hQ (r+routingB P.M.base A.reindex)+
        routingA P.M.base A.reindex*(symmetricPrefixRouting A hQ).u r := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  exact (symmetricPrefixIdeal A hQ).apery_step_eq _ _ (routingHB _ _) r
private theorem prefix_c_step (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (r : ZMod (routingA P.M.base A.reindex)) :
    symmetricPrefixLambda A hQ r+routingC P.M.base A.reindex=
      symmetricPrefixLambda A hQ (r+routingC P.M.base A.reindex)+
        routingA P.M.base A.reindex*(symmetricPrefixRouting A hQ).v r := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  exact (symmetricPrefixIdeal A hQ).apery_step_eq _ _ (routingHC _ _) r

/-- The exact corner resource of the actual prefix graph. Its defects are
the maximum actual return depth; opposite-edge zeros come from S8 and
the graph's proved diamond identity, not from its fake-seat tag. -/
theorem symmetric_prefix_kappa_unused (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    L5A2C4I.ResidueData.ExactUnusedMergeReverseBase (symmetricPrefixRouting A hQ)
      (gridResidue P.M.base A.reindex (ciH A-1) (ciG A-1)) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  obtain ⟨ellMax,hmax⟩ := symmetric_return_depth_maximum A hB hQ
  let dep := (symmetricReturnTuple A hB ellMax).2.2
  let D := symmetricPrefixRouting A hQ
  let kap := gridResidue P.M.base A.reindex (ciH A-1) (ciG A-1)
  have S := symmetricReturnTuple_spec A hB ellMax
  have hh := (symmetric_ci_normalized_equations A).2.1
  have hg := (symmetric_ci_normalized_equations A).1
  have hvh := (symmetric_ci_normalized_equations A).2.2.2.1
  have hdK := S.2.2.2.2.2.1
  have hdP := S.2.2.2.2.1
  have ha : (0 : ℤ)<n0 A := by exact_mod_cast (branchA_symmetricTailData A).n0_pos
  have hhZ : ((ciH A-1 : ℕ) : ℤ)+1=ciH A := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ ciH A)
  have hgZ : ((ciG A-1 : ℕ) : ℤ)+1=ciG A := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ ciG A)
  have hkd : ((ciK A-dep : ℕ) : ℤ)+dep=ciK A := by exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hdK)
  have hpure : (ciH A : ℤ)*n1 A=ciK A*n0 A := by exact_mod_cast symmetric_ci_b_carry A
  have hmixed : (ciG A : ℤ)*n2 A=ciU A*n0 A+ciV A*n1 A := by exact_mod_cast mixed_carry A
  have hkap := symmetric_prefix_kappa_height_zero A hB hQ
  have hbot := symmetric_prefix_corner_b_height_exact A hB hQ ellMax hmax
  have hb := prefix_b_step A hQ kap
  dsimp only [kap] at hb
  rw [hkap,grid_add_b,Nat.sub_add_cancel (by omega : 1 ≤ ciH A),grid_b_wrap,hbot,
    routingB_eq_n1 A] at hb
  simp only [routingA_eq_n0 A] at hb
  have hu : D.u kap=dep := by
    have he : ((D.u kap : ℕ) : ℤ)=dep := by
      change _+_=_+_*(D.u kap : ℤ) at hb
      simp only [Nat.cast_add,Nat.cast_mul] at hb
      nlinarith only [hb,hhZ,hkd,hpure,ha]
    exact_mod_cast he
  have h00 : symmetricPrefixLambda A hQ (gridResidue P.M.base A.reindex (ciV A) 0)=
      ((ciU A+ciK A-dep)*n0 A+ciV A*n1 A : ℕ) := by
    by_cases hz : ciV A=0
    · have he := (symmetric_prefix_corner_c_height_exact_of_zero A hB hQ ellMax hmax hz).2
      simpa only [hz,zero_mul,add_zero] using he
    · exact symmetric_prefix_corner_c_height_exact_of_pos A hB hQ ellMax hmax (by omega) (by omega) (le_refl _)
  have hUD : dep ≤ ciU A+ciK A := by dsimp [dep]; omega
  have hUKd : ((ciU A+ciK A-dep : ℕ) : ℤ)+dep=(ciU A+ciK A : ℕ) := by
    exact_mod_cast Nat.sub_add_cancel hUD
  have hbv := prefix_c_step A hQ (gridResidue P.M.base A.reindex 0 (ciG A-1))
  have hVmod : (0+ciV A)%ciH A=ciV A := by simpa only [zero_add] using Nat.mod_eq_of_lt hvh
  rw [hbot,grid_add_c,Nat.sub_add_cancel (by omega : 1 ≤ ciG A),grid_c_wrap,hVmod,h00,
    routingC_eq_n2 A] at hbv
  simp only [routingA_eq_n0 A] at hbv
  have hvb : D.v (D.b kap)=0 := by
    have he : ((D.v (gridResidue P.M.base A.reindex 0 (ciG A-1)) : ℕ) : ℤ)=0 := by
      change _+_=_+_*(D.v (gridResidue P.M.base A.reindex 0 (ciG A-1)) : ℤ) at hbv
      simp only [Nat.cast_add,Nat.cast_mul] at hbv hUKd hmixed
      nlinarith only [hbv,hgZ,hkd,hUKd,hmixed,ha]
    change D.v (kap+routingB P.M.base A.reindex)=0
    dsimp only [kap]
    rw [grid_add_b,Nat.sub_add_cancel (by omega : 1 ≤ ciH A),grid_b_wrap]
    exact_mod_cast he
  have hc := prefix_c_step A hQ kap
  dsimp only [kap] at hc
  rw [hkap,grid_add_c,Nat.sub_add_cancel (by omega : 1 ≤ ciG A),grid_c_wrap,
    routingC_eq_n2 A] at hc
  simp only [routingA_eq_n0 A] at hc
  have hv : D.v kap=dep := by
    by_cases hz : ciV A=0
    · have hmod : (ciH A-1+ciV A)%ciH A=ciH A-1 := by
        simpa only [hz,add_zero] using Nat.mod_eq_of_lt (by omega : ciH A-1 < ciH A)
      rw [hmod,(symmetric_prefix_corner_c_height_exact_of_zero A hB hQ ellMax hmax hz).1] at hc
      have hdU : dep < ciU A := by
        have hd := S.2.2.2.2.2.2.1
        simpa only [hz,add_zero,Nat.div_eq_of_lt S.2.1,zero_mul,add_zero] using hd
      have hUd : ((ciU A-dep : ℕ) : ℤ)+dep=ciU A := by exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hdU)
      have he : ((D.v kap : ℕ) : ℤ)=dep := by
        change _+_=_+_*(D.v kap : ℤ) at hc
        simp only [Nat.cast_add,Nat.cast_mul] at hc
        rw [hz,Nat.cast_zero,zero_mul,add_zero] at hmixed
        nlinarith only [hc,hgZ,hUd,hmixed,ha]
      exact_mod_cast he
    · have hpos : 0 < ciV A := by omega
      have hsum : ciH A-1+ciV A=(ciV A-1)+ciH A := by omega
      have hmod : (ciH A-1+ciV A)%ciH A=ciV A-1 := by
        rw [hsum,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : ciV A-1 < ciH A)]
      have hend := symmetric_prefix_corner_c_height_exact_of_pos A hB hQ ellMax hmax hpos
        (x := ciV A-1) (le_refl _) (by omega)
      rw [hmod,hend] at hc
      have hVm : ((ciV A-1 : ℕ) : ℤ)+1=ciV A := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ ciV A)
      have he : ((D.v kap : ℕ) : ℤ)=dep := by
        change _+_=_+_*(D.v kap : ℤ) at hc
        simp only [Nat.cast_add,Nat.cast_mul] at hc hUKd hmixed
        nlinarith only [hc,hgZ,hhZ,hVm,hUKd,hmixed,hpure,ha]
      exact_mod_cast he
  have hdiamond := D.diamond kap
  rw [hu,hv,hvb] at hdiamond
  refine ⟨hu.trans hv.symm,?_,?_,hvb⟩
  · rw [hu]
    exact hdP
  · change D.u (D.c kap)=0
    omega

theorem symmetric_prefix_fakeSeat_unique (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    ∀ s : FakeSink (symmetricPrefixIdeal A hQ) (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _),
    s.val=gridResidue P.M.base A.reindex (ciH A-1) (ciG A-1) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  intro s
  have hs := s.property.1
  have hn := s.property.2
  change (symmetricPrefixRouting A hQ).IsSink s.val at hs
  change symmetricPrefixLambda A hQ s.val-routingA P.M.base A.reindex ∉
    (routingH P.M.base A.reindex).asRelativeIdeal at hn
  have hm := (symmetricPrefixIdeal A hQ).aperyRepresentative_mem
    (routingA P.M.base A.reindex) s.val
  obtain ⟨ell,hp,hl,hret⟩ := hm
  obtain ⟨w,hw,he⟩ := hret.1
  obtain ⟨p,x,y,hx,hy,hf⟩ := branchA_routingH_rectangle_factorization A hw
  change x < ciH A at hx
  change y < ciG A at hy
  rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A] at hf
  have hz : symmetricPrefixLambda A hQ s.val=(p*n0 A+x*n1 A+y*n2 A : ℕ) := by
    change symmetricPrefixLambda A hQ s.val=(w : ℤ) at he
    rw [he,hf]
  have hp0 : p=0 := by
    by_contra hp0
    have hp1 : p=p-1+1 := by omega
    apply hn
    simp only [routingA_eq_n0 A,hz]
    have hmH := gridH A (p-1) x y
    have heq : ((p*n0 A+x*n1 A+y*n2 A : ℕ) : ℤ)-n0 A=
        ((p-1)*n0 A+x*n1 A+y*n2 A : ℕ) := by
      have heZ : (p : ℤ)=(p-1 : ℕ)+1 := by exact_mod_cast hp1
      simp only [Nat.cast_add,Nat.cast_mul]
      nlinarith only [heZ]
    rw [heq]
    exact hmH
  rw [hp0,zero_mul,zero_add] at hz
  have hmod := (symmetricPrefixIdeal A hQ).aperyRepresentative_mod (routingA P.M.base A.reindex) s.val
  change (symmetricPrefixLambda A hQ s.val : ZMod (routingA P.M.base A.reindex))=s.val at hmod
  rw [hz] at hmod
  have hgrid : s.val=gridResidue P.M.base A.reindex x y := by
    have hh := nat_grid_mod A 0 x y
    simp only [zero_mul,zero_add] at hh
    exact hmod.symm.trans (by exact_mod_cast hh)
  rw [hgrid] at hs hz
  have hquad := (symmetric_prefix_height_zero_iff_F_quadrant A hB hQ hx hy).mp hz
  have hhP := (symmetric_ci_normalized_equations A).2.1
  have hgP := (symmetric_ci_normalized_equations A).1
  have hxend : x=ciH A-1 := by
    by_contra hne
    have hxs : x+1 < ciH A := by omega
    have hnext := (symmetric_prefix_height_zero_iff_F_quadrant A hB hQ hxs hy).mpr
      (by obtain ⟨l,hi,hj⟩ := hquad; exact ⟨l,by omega,hj⟩)
    have he := prefix_b_step A hQ (gridResidue P.M.base A.reindex x y)
    rw [hz,grid_add_b,hnext,routingB_eq_n1 A] at he
    have ha : (0 : ℤ)<routingA P.M.base A.reindex := by exact_mod_cast routingA_pos P.M.base A.reindex
    have hu : (symmetricPrefixRouting A hQ).u (gridResidue P.M.base A.reindex x y)=0 := by
      have heZ : ((symmetricPrefixRouting A hQ).u (gridResidue P.M.base A.reindex x y) : ℤ)=0 := by
        simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at he
        nlinarith only [he,ha]
      exact_mod_cast heZ
    exact hs.1 hu
  have hyend : y=ciG A-1 := by
    by_contra hne
    have hys : y+1 < ciG A := by omega
    have hnext := (symmetric_prefix_height_zero_iff_F_quadrant A hB hQ hx hys).mpr
      (by obtain ⟨l,hi,hj⟩ := hquad; exact ⟨l,hi,by omega⟩)
    have he := prefix_c_step A hQ (gridResidue P.M.base A.reindex x y)
    rw [hz,grid_add_c,hnext,routingC_eq_n2 A] at he
    have ha : (0 : ℤ)<routingA P.M.base A.reindex := by exact_mod_cast routingA_pos P.M.base A.reindex
    have hv : (symmetricPrefixRouting A hQ).v (gridResidue P.M.base A.reindex x y)=0 := by
      have heZ : ((symmetricPrefixRouting A hQ).v (gridResidue P.M.base A.reindex x y) : ℤ)=0 := by
        simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at he
        nlinarith only [he,ha]
      exact_mod_cast heZ
    exact hs.2 hv
  simpa only [hxend,hyend] using hgrid

theorem symmetric_prefix_fakeSinkCount_eq_one (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    fakeSinkCount (symmetricPrefixIdeal A hQ) (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _)=1 := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  let E : FakeSink (symmetricPrefixIdeal A hQ) (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _) ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => symmetric_prefix_kappa_fakeSeat A hB hQ
      left_inv := fun s => Subtype.ext ((symmetric_prefix_fakeSeat_unique A hB hQ s).symm)
      right_inv := fun _ => rfl }
  exact (Nat.card_congr E).trans (Nat.card_unique (α := Unit))

end NS25Lean.L5A2BFinalRepair
