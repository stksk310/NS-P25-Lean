import NS25Lean.P3IdealHeightsR61
import NS25Lean.P3HerzogGridR61

set_option linter.style.header false
set_option maxHeartbeats 800000
noncomputable section
namespace NS25Lean.P3R63
open CombinatorialCore L5A2C4I

/-- A finite zero corridor controls the literal frozen final endpoint. -/
theorem c_endpoint_zero_of_corridor {R : Type*} [Fintype R]
    (D : ResidueData R) (s : ResidueData.CSourceTargetBranches D)
    (N : ℕ) (hN : 0 < N) (hz : D.u ((D.c ^ N) s.val) = 0)
    (hcorr : ∀ k : ℕ, 0 < k → k < N → D.v (D.b ((D.c ^ k) s.val)) = 0) :
    ResidueData.CFirstStageNonexceptional D s := by
  let n := ResidueData.cFirstZeroIndex D s
  have hn : 0 < n := ResidueData.firstZeroIndex_pos D.c D.u s.val s.property.1.1
  have hnle : n ≤ N := by
    unfold n ResidueData.cFirstZeroIndex ResidueData.firstZeroIndex
    exact Nat.find_min' _ ⟨hN, hz⟩
  have hn2 : 1 < n := by
    have hp := (ResidueData.sourceTargetBranch_iff_positive_cross D).mp s.property |>.2.2
    have hzero := ResidueData.firstZeroIndex_zero D.c D.u s.val s.property.1.1
    by_contra h
    have he : n = 1 := by omega
    change D.u ((D.c ^ n) s.val) = 0 at hzero
    rw [he] at hzero
    simp only [pow_one] at hzero
    omega
  exact hcorr (n-1) (by omega) (by omega)

variable {H : NumericalSemigroup} (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H)

private theorem actual_rep_of_canonical_mem
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (x : ℤ)
    (hcan : H.asRelativeIdeal.aperyRepresentative a (x : ZMod a) = x)
    (hx : x ∈ I) : I.aperyRepresentative a (x : ZMod a) = x := by
  apply le_antisymm (I.aperyRepresentative_le a _ hx rfl)
  have h := H.asRelativeIdeal.aperyRepresentative_le a (x : ZMod a)
    (hsub _ (I.aperyRepresentative_mem a (x : ZMod a))) (I.aperyRepresentative_mod a _)
  simpa [hcan] using h

private theorem actual_step_zero (d : ℕ) (hd : d ∈ H) (x : ℤ)
    (h0 : I.aperyRepresentative a (x : ZMod a) = x)
    (h1 : I.aperyRepresentative a ((x+d : ℤ) : ZMod a) = x+d) :
    I.aperyStepQuotient a d hd (x : ZMod a) = 0 := by
  have he := I.apery_step_eq a d hd (x : ZMod a)
  have h1' : I.aperyRepresentative a ((x : ZMod a)+d) = x+d := by simpa using h1
  rw [h0,h1'] at he
  have ha : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have hz : (I.aperyStepQuotient a d hd (x : ZMod a) : ℤ) = 0 := by nlinarith
  exact_mod_cast hz

private theorem actual_step_zero_nat (d : ℕ) (hd : d ∈ H) (x : ℕ)
    (h0 : I.aperyRepresentative a ((x : ℤ) : ZMod a) = x)
    (h1 : I.aperyRepresentative a (((x : ℤ)+d : ℤ) : ZMod a) = (x : ℤ)+d) :
    I.aperyStepQuotient a d hd (x : ZMod a) = 0 := by
  simpa only [Int.cast_natCast] using actual_step_zero I a d hd (x : ℤ) h0 h1

private theorem c_iterate (s : ZMod a) (k : ℕ) :
    ((P3R60.idealData I a b c hb hc).c ^ k) s = s + k * (c : ZMod a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    change s + k * (c : ZMod a) + c = s + ((k+1 : ℕ) : ZMod a) * (c : ZMod a)
    push_cast
    ring

include hb hc in
/-- Actual ideal membership propagates northeast in the bc grid. -/
theorem grid_mem_of_le (i j x y : ℕ) (hi : i ≤ x) (hj : j ≤ y)
    (hm : ((i*b+j*c : ℕ) : ℤ) ∈ I) : ((x*b+y*c : ℕ) : ℤ) ∈ I := by
  have hb' : (x-i)*b ∈ H := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using H.toAddSubmonoid.nsmul_mem hb (x-i)
  have hc' : (y-j)*c ∈ H := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using H.toAddSubmonoid.nsmul_mem hc (y-j)
  have hadd := I.add_mem_nat hm (H.add_mem hb' hc')
  convert hadd using 1 <;> push_cast <;> nlinarith [Nat.sub_add_cancel hi,Nat.sub_add_cancel hj]

include hb hc in
/-- Minimality of the actual generators supplies the coordinate antichain. -/
theorem minimal_grid_antichain (hbpos : 0 < b) (hcpos : 0 < c)
    (i j x y : ℕ) (hmin : I.IsMinimalGenerator ((i*b+j*c : ℕ) : ℤ))
    (hm : ((x*b+y*c : ℕ) : ℤ) ∈ I) (hi : x ≤ i) (hj : y ≤ j) : i = x ∧ j = y := by
  have hb' : (i-x)*b ∈ H := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using H.toAddSubmonoid.nsmul_mem hb (i-x)
  have hc' : (j-y)*c ∈ H := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using H.toAddSubmonoid.nsmul_mem hc (j-y)
  by_contra hne
  have hd : (i-x)*b+(j-y)*c ≠ 0 := by
    intro hz
    have hi' : i-x = 0 := by nlinarith
    have hj' : j-y = 0 := by nlinarith
    exact hne ⟨by omega,by omega⟩
  apply hmin.2 _ (H.add_mem hb' hc') hd
  convert hm using 1 <;> push_cast <;> nlinarith [Nat.sub_add_cancel hi,Nat.sub_add_cancel hj]

end NS25Lean.P3R63

namespace NS25Lean.P3R63
open CombinatorialCore L5A2C4I
variable {H : NumericalSemigroup} (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H)

/-- The target equality fixes the actual seed, without any endpoint certificate. -/
theorem seed_of_target_grid
    (s : ResidueData.CSourceTargetBranches (P3R60.idealData I a b c hb hc))
    (i j : ℕ)
    (ht : I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val) =
      ((i*b+j*c : ℕ) : ℤ)) :
    s.val = ((((i*b+j*c : ℕ) : ℤ)-b-c) : ZMod a) := by
  have he := I.aperyRepresentative_mod a ((P3R60.idealData I a b c hb hc).branchTarget s.val)
  rw [ht] at he
  change (((i*b+j*c : ℕ) : ℤ) : ZMod a) = s.val + b + c at he
  push_cast at he ⊢
  linear_combination -he

private theorem iterate_grid
    (s : ZMod a) (i j : ℕ) (hi : 0 < i) (hj : 0 < j)
    (hs : s = ((((i*b+j*c : ℕ) : ℤ)-b-c) : ZMod a)) (k : ℕ) :
    ((P3R60.idealData I a b c hb hc).c ^ k) s =
      (((i-1)*b+(j-1+k)*c : ℕ) : ZMod a) := by
  rw [c_iterate I a b c hb hc, hs]
  have hei : i-1+1=i := by omega
  have hej : j-1+1=j := by omega
  have hei' := congrArg (fun n : ℕ => (n : ZMod a)) hei
  have hej' := congrArg (fun n : ℕ => (n : ZMod a)) hej
  push_cast at hei' hej' ⊢
  linear_combination -b * hei' - c * hej'

/-- The zero rectangle makes the later-column seed nonexceptional in the final
ideal itself. All cells and all edges here are literal final ideal data. -/
theorem c_nonexceptional_of_left_target
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (B C : ℕ)
    (hcan : ∀ x y : ℕ, x < B → y < C →
      H.asRelativeIdeal.aperyRepresentative a (((x*b+y*c : ℕ) : ℤ) : ZMod a) =
        ((x*b+y*c : ℕ) : ℤ))
    (s : ResidueData.CSourceTargetBranches (P3R60.idealData I a b c hb hc))
    (i j x y : ℕ) (hi : 0 < i) (hj : 0 < j) (hiB : i < B) (hyC : y < C)
    (hxi : x < i) (hjy : j < y)
    (ht : I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val) =
      ((i*b+j*c : ℕ) : ℤ))
    (hm : ((x*b+y*c : ℕ) : ℤ) ∈ I) :
    ResidueData.CFirstStageNonexceptional (P3R60.idealData I a b c hb hc) s := by
  let D := P3R60.idealData I a b c hb hc
  have hs := seed_of_target_grid I a b c hb hc s i j ht
  have him : ((i*b+j*c : ℕ) : ℤ) ∈ I := by
    rw [← ht]; exact I.aperyRepresentative_mem a _
  have hrep (r t : ℕ) (hr : r < B) (ht' : t < C)
      (hm' : ((r*b+t*c : ℕ) : ℤ) ∈ I) :
      I.aperyRepresentative a (((r*b+t*c : ℕ) : ℤ) : ZMod a) = ((r*b+t*c : ℕ) : ℤ) :=
    actual_rep_of_canonical_mem I a hsub _ (hcan r t hr ht') hm'
  have hright (t : ℕ) (hjt : j ≤ t) (hty : t ≤ y) :
      I.aperyRepresentative a (((i*b+t*c : ℕ) : ℤ) : ZMod a) = ((i*b+t*c : ℕ) : ℤ) := by
    exact hrep i t hiB (by omega) (grid_mem_of_le I b c hb hc i j i t le_rfl hjt him)
  have hleft : I.aperyRepresentative a ((((i-1)*b+y*c : ℕ) : ℤ) : ZMod a) =
      (((i-1)*b+y*c : ℕ) : ℤ) := by
    exact hrep (i-1) y (by omega) hyC
      (grid_mem_of_le I b c hb hc x y (i-1) y (by omega) le_rfl hm)
  let N := y-j+1
  apply c_endpoint_zero_of_corridor D s N (by dsimp [N]; omega)
  · have he := iterate_grid I a b c hb hc s.val i j hi hj hs N
    have hcoord : j-1+N=y := by dsimp [N]; omega
    rw [hcoord] at he
    change I.aperyStepQuotient a b hb ((D.c ^ N) s.val) = 0
    rw [he]
    apply actual_step_zero_nat I a b hb ((i-1)*b+y*c) hleft
    have heint : (((i-1)*b+y*c : ℕ) : ℤ)+b = ((i*b+y*c : ℕ) : ℤ) := by
      push_cast
      have heI : ((i-1 : ℕ) : ℤ)+1 = i := by omega
      nlinarith
    rw [heint]
    exact hright y (by omega) le_rfl
  · intro k hk hkN
    have he := iterate_grid I a b c hb hc s.val i j hi hj hs k
    have hbk : D.b ((D.c ^ k) s.val) = ((i*b+(j-1+k)*c : ℕ) : ZMod a) := by
      rw [he]
      change (((i-1)*b+(j-1+k)*c : ℕ) : ZMod a) + b = _
      have hei := congrArg (fun n : ℕ => (n : ZMod a))
        (show i-1+1=i by omega)
      push_cast at hei ⊢
      linear_combination b * hei
    change I.aperyStepQuotient a c hc (D.b ((D.c ^ k) s.val)) = 0
    rw [hbk]
    apply actual_step_zero_nat I a c hc (i*b+(j-1+k)*c)
      (hright (j-1+k) (by omega) (by dsimp [N] at hkN; omega))
    have heint : ((i*b+(j-1+k)*c : ℕ) : ℤ)+c = ((i*b+(j-1+k+1)*c : ℕ) : ℤ) := by
      push_cast
      ring
    rw [heint]
    exact hright (j-1+k+1) (by omega) (by dsimp [N] at hkN; omega)

end NS25Lean.P3R63


namespace NS25Lean.P3R63
open CombinatorialCore L5A2C4I
variable {H : NumericalSemigroup} (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H)

/-- Canonical targets in one genuine rectangle force the actual final exceptional
count to be at most one. The antichain comes from actual generator minimality. -/
theorem cExceptionalCount_le_one_of_rectangle
    (hgen : H.IsGeneratedByThree a b c) (hbpos : 0 < b) (hcpos : 0 < c)
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (B C : ℕ)
    (hcan : ∀ x y : ℕ, x < B → y < C →
      H.asRelativeIdeal.aperyRepresentative a (((x*b+y*c : ℕ) : ℤ) : ZMod a) =
        ((x*b+y*c : ℕ) : ℤ))
    (htargets : ∀ s : ResidueData.CSourceTargetBranches (P3R60.idealData I a b c hb hc),
      ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ i < B ∧ j < C ∧
        I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val) =
          ((i*b+j*c : ℕ) : ℤ)) :
    ResidueData.cExceptionalCount (P3R60.idealData I a b c hb hc) ≤ 1 := by
  let D := P3R60.idealData I a b c hb hc
  have hminimal (s : ResidueData.CSourceTargetBranches D) :
      I.IsMinimalGenerator (I.aperyRepresentative a (D.branchTarget s.val)) :=
    (I.concrete_isSource_iff_isMinimalGenerator a b c hgen hb hc
      (Nat.ne_of_gt hbpos) (Nat.ne_of_gt hcpos) _).mp s.property.2
  have hcol (s : ResidueData.CExceptionalBranches D)
      (t : ResidueData.CSourceTargetBranches D) (i j x y : ℕ)
      (hi : 0 < i) (hj : 0 < j) (hiB : i < B) (hyC : y < C)
      (hs : I.aperyRepresentative a (D.branchTarget s.val.val) = ((i*b+j*c : ℕ) : ℤ))
      (ht : I.aperyRepresentative a (D.branchTarget t.val) = ((x*b+y*c : ℕ) : ℤ)) : i ≤ x := by
    by_contra hn
    have hxi : x < i := by omega
    have hm : ((x*b+y*c : ℕ) : ℤ) ∈ I := by
      rw [← ht]; exact I.aperyRepresentative_mem a _
    have hjy : j < y := by
      by_contra hn'
      have hmin := hminimal s.val
      rw [hs] at hmin
      have he := minimal_grid_antichain I b c hb hc hbpos hcpos i j x y hmin hm
        (by omega) (by omega)
      omega
    exact s.property (c_nonexceptional_of_left_target I a b c hb hc hsub B C hcan
      s.val i j x y hi hj hiB hyC hxi hjy hs hm)
  have hsubsingle : Subsingleton (ResidueData.CExceptionalBranches D) := by
    constructor
    intro s t
    obtain ⟨i,j,hi,hj,hiB,hjC,hs⟩ := htargets s.val
    obtain ⟨x,y,hx,hy,hxB,hyC,ht⟩ := htargets t.val
    have hix := hcol s t.val i j x y hi hj hiB hyC hs ht
    have hxi := hcol t s.val x y i j hx hy hxB hjC ht hs
    have heI : i = x := by omega
    have hminS := hminimal s.val
    have hminT := hminimal t.val
    rw [hs] at hminS
    rw [ht] at hminT
    have hmS : ((i*b+j*c : ℕ) : ℤ) ∈ I := hminS.1
    have hmT : ((x*b+y*c : ℕ) : ℤ) ∈ I := hminT.1
    have heJ : j = y := by
      rcases le_total j y with hjy | hyj
      · exact (minimal_grid_antichain I b c hb hc hbpos hcpos x y i j hminT hmS
          hix hjy).2.symm
      · exact (minimal_grid_antichain I b c hb hc hbpos hcpos i j x y hminS hmT
          hxi hyj).2
    have hw : I.aperyRepresentative a (D.branchTarget s.val.val) =
        I.aperyRepresentative a (D.branchTarget t.val.val) := by rw [hs,ht,heI,heJ]
    have hr := congrArg (fun z : ℤ => (z : ZMod a)) hw
    rw [I.aperyRepresentative_mod,I.aperyRepresentative_mod] at hr
    exact Subtype.ext (Subtype.ext (D.branchTarget_injective hr))
  have hinj : Function.Injective (fun _ : ResidueData.CExceptionalBranches D => ()) :=
    fun s t _ => hsubsingle.elim s t
  exact le_trans (Nat.card_le_card_of_injective _ hinj) (by simp)

end NS25Lean.P3R63




namespace NS25Lean.P3R63
open CombinatorialCore L5A2C4I
variable {H : NumericalSemigroup} (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H)

/-- The transposed rectangle bound, transported through the frozen concrete
b/c swap on the same actual ideal and the same residue carrier. -/
theorem bExceptionalCount_le_one_of_rectangle
    (hgen : H.IsGeneratedByThree a b c) (hbpos : 0 < b) (hcpos : 0 < c)
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (B C : ℕ)
    (hcan : ∀ x y : ℕ, x < B → y < C →
      H.asRelativeIdeal.aperyRepresentative a (((x*b+y*c : ℕ) : ℤ) : ZMod a) =
        ((x*b+y*c : ℕ) : ℤ))
    (htargets : ∀ s : ResidueData.CSourceTargetBranches (P3R60.idealData I a b c hb hc),
      ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ i < B ∧ j < C ∧
        I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val) =
          ((i*b+j*c : ℕ) : ℤ)) :
    ResidueData.bExceptionalCount (P3R60.idealData I a b c hb hc) ≤ 1 := by
  have hswap := P3R57.concrete_cExceptional_swap I I a a b c c b hb hc hc hb
    rfl rfl rfl rfl
  change ResidueData.cExceptionalCount (P3R60.idealData I a c b hc hb) =
    ResidueData.bExceptionalCount (P3R60.idealData I a b c hb hc) at hswap
  rw [← hswap]
  have hgen' : H.IsGeneratedByThree a c b := by
    simpa only [NumericalSemigroup.IsGeneratedByThree, Set.pair_comm] using hgen
  apply cExceptionalCount_le_one_of_rectangle I a c b hc hb hgen' hcpos hbpos hsub C B
  · intro x y hx hy
    simpa only [Nat.add_comm] using hcan y x hy hx
  · intro s
    have he : P3R60.idealData I a c b hc hb =
        P3R57.swapData (P3R60.idealData I a b c hb hc) := rfl
    let t : ResidueData.CSourceTargetBranches (P3R60.idealData I a b c hb hc) :=
      ⟨s.val, (P3R57.sourceTargetBranch_swap _ s.val).mp (he ▸ s.property)⟩
    obtain ⟨i,j,hi,hj,hiB,hjC,ht⟩ := htargets t
    refine ⟨j,i,hj,hi,hjC,hiB,?_⟩
    have htarget : (P3R60.idealData I a c b hc hb).branchTarget s.val =
        (P3R60.idealData I a b c hb hc).branchTarget t.val := by
      change s.val+c+b = s.val+b+c
      abel
    rw [htarget]
    simpa only [Nat.add_comm] using ht

end NS25Lean.P3R63
