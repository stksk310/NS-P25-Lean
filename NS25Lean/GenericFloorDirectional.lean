import NS25Lean.P3R3StaircaseR67
import NS25Lean.P3R2ZeroRectangleR63

set_option autoImplicit false
set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.GenericFloorDirectional
open CombinatorialCore L5A2C4I P3R67
variable {H : NumericalSemigroup}

private theorem c_iterate (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) (s : ZMod a) (k : ℕ) :
    ((P3R60.idealData I a b c hb hc).c ^ k) s = s+k*(c:ZMod a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih]
    change s+k*(c:ZMod a)+c=s+((k+1:ℕ):ZMod a)*(c:ZMod a)
    push_cast
    ring

/-- Only the positive iterate is indexed by natural rows. The original
seed is kept as an integer, so a target on row zero is admitted. -/
private theorem positive_iterate_grid (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) (s : ZMod a) (i j k : ℕ)
    (hi : 0 < i) (hk : 0 < k)
    (hs : s=((((i*b+j*c:ℕ):ℤ)-b-c):ZMod a)) :
    ((P3R60.idealData I a b c hb hc).c^k) s=
      (((i-1)*b+(j+k-1)*c:ℕ):ZMod a) := by
  rw [c_iterate I a b c hb hc,hs]
  have hei:=congrArg (fun n : ℕ=>(n:ZMod a)) (show i-1+1=i by omega)
  have hej:=congrArg (fun n : ℕ=>(n:ZMod a)) (show j+k-1+1=j+k by omega)
  push_cast at hei hej ⊢
  linear_combination -b*hei-c*hej

private theorem step_zero_nat (I : RelativeIdeal H) (a d : ℕ) [NeZero a]
    (hd : d∈H) (x : ℕ)
    (h0 : I.aperyRepresentative a ((x:ℤ):ZMod a)=x)
    (h1 : I.aperyRepresentative a (((x:ℤ)+d:ℤ):ZMod a)=(x:ℤ)+d) :
    I.aperyStepQuotient a d hd (x:ZMod a)=0 := by
  simpa only [Int.cast_natCast] using final_step_zero_of_representatives I a d hd (x:ℤ) h0 h1

/-- The actual first c-endpoint from a zero strictly left and above.
The target's second coordinate is allowed to be zero. -/
theorem c_nonexceptional_of_left_zero (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b∈H) (hc : c∈H)
    (hsub : ∀ z : ℤ, z∈I → z∈H.asRelativeIdeal) (Imax Jmax : ℕ)
    (hcan : ∀ x y : ℕ, x<Imax → y<Jmax →
      H.asRelativeIdeal.aperyRepresentative a (((x*b+y*c:ℕ):ℤ):ZMod a)=((x*b+y*c:ℕ):ℤ))
    (s : ResidueData.CSourceTargetBranches (P3R60.idealData I a b c hb hc))
    (i j x y : ℕ) (hiI : i < Imax) (hyJ : y < Jmax) (hxi : x < i) (hjy : j < y)
    (ht : I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val)=
      ((i*b+j*c:ℕ):ℤ))
    (hm : ((x*b+y*c:ℕ):ℤ)∈I) :
    ResidueData.CFirstStageNonexceptional (P3R60.idealData I a b c hb hc) s := by
  let D:=P3R60.idealData I a b c hb hc
  have hi : 0 < i := by omega
  have hs:=P3R63.seed_of_target_grid I a b c hb hc s i j ht
  have him : ((i*b+j*c:ℕ):ℤ)∈I := by
    rw [←ht]
    exact I.aperyRepresentative_mem a _
  have hrep (r t : ℕ) (hr : r<Imax) (ht' : t<Jmax)
      (hm' : ((r*b+t*c:ℕ):ℤ)∈I) :
      I.aperyRepresentative a (((r*b+t*c:ℕ):ℤ):ZMod a)=((r*b+t*c:ℕ):ℤ) :=
    final_rep_of_canonical_mem I a hsub _ (hcan r t hr ht') hm'
  have hright (t : ℕ) (hjt : j≤t) (hty : t≤y) :
      I.aperyRepresentative a (((i*b+t*c:ℕ):ℤ):ZMod a)=((i*b+t*c:ℕ):ℤ) := by
    exact hrep i t hiI (by omega) (P3R63.grid_mem_of_le I b c hb hc i j i t le_rfl hjt him)
  have hleft : I.aperyRepresentative a ((((i-1)*b+y*c:ℕ):ℤ):ZMod a)=
      (((i-1)*b+y*c:ℕ):ℤ) := by
    exact hrep (i-1) y (by omega) hyJ
      (P3R63.grid_mem_of_le I b c hb hc x y (i-1) y (by omega) le_rfl hm)
  let N:=y-j+1
  apply P3R63.c_endpoint_zero_of_corridor D s N (by dsimp [N];omega)
  · have he:=positive_iterate_grid I a b c hb hc s.val i j N hi (by dsimp [N];omega) hs
    have hcoord : j+N-1=y := by dsimp [N];omega
    rw [hcoord] at he
    change I.aperyStepQuotient a b hb ((D.c^N) s.val)=0
    rw [he]
    apply step_zero_nat I a b hb ((i-1)*b+y*c) hleft
    have heint : (((i-1)*b+y*c:ℕ):ℤ)+b=((i*b+y*c:ℕ):ℤ) := by
      push_cast
      have hI : ((i-1:ℕ):ℤ)+1=i := by omega
      nlinarith
    rw [heint]
    exact hright y (by omega) le_rfl
  · intro k hk hkN
    have he:=positive_iterate_grid I a b c hb hc s.val i j k hi hk hs
    have hbk : D.b ((D.c^k) s.val)=((i*b+(j+k-1)*c:ℕ):ZMod a) := by
      rw [he]
      change (((i-1)*b+(j+k-1)*c:ℕ):ZMod a)+b=_
      have hei:=congrArg (fun n : ℕ=>(n:ZMod a)) (show i-1+1=i by omega)
      push_cast at hei ⊢
      linear_combination b*hei
    change I.aperyStepQuotient a c hc (D.b ((D.c^k) s.val))=0
    rw [hbk]
    apply step_zero_nat I a c hc (i*b+(j+k-1)*c)
      (hright (j+k-1) (by omega) (by dsimp [N] at hkN;omega))
    have heint : ((i*b+(j+k-1)*c:ℕ):ℤ)+c=((i*b+(j+k-1+1)*c:ℕ):ℤ) := by
      push_cast
      ring
    rw [heint]
    exact hright (j+k-1+1) (by omega) (by dsimp [N] at hkN;omega)

/-- Literal b-direction counterpart; the target's first coordinate may be zero. -/
theorem b_nonexceptional_of_right_zero (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b∈H) (hc : c∈H)
    (hsub : ∀ z : ℤ, z∈I → z∈H.asRelativeIdeal) (Imax Jmax : ℕ)
    (hcan : ∀ x y : ℕ, x<Imax → y<Jmax →
      H.asRelativeIdeal.aperyRepresentative a (((x*b+y*c:ℕ):ℤ):ZMod a)=((x*b+y*c:ℕ):ℤ))
    (s : ResidueData.BSourceTargetBranches (P3R60.idealData I a b c hb hc))
    (i j x y : ℕ) (hjJ : j<Jmax) (hxI : x<Imax) (hix : i<x) (hyj : y<j)
    (ht : I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val)=
      ((i*b+j*c:ℕ):ℤ))
    (hm : ((x*b+y*c:ℕ):ℤ)∈I) :
    ResidueData.BFirstStageNonexceptional (P3R60.idealData I a b c hb hc) s := by
  let D:=P3R60.idealData I a b c hb hc
  let t : ResidueData.CSourceTargetBranches (P3R60.idealData I a c b hc hb):=
    ⟨s.val,(P3R57.sourceTargetBranch_swap D s.val).mpr s.property⟩
  have htarget : (P3R60.idealData I a c b hc hb).branchTarget t.val=D.branchTarget s.val := by
    change s.val+c+b=s.val+b+c
    abel
  have hnon:=c_nonexceptional_of_left_zero I a c b hc hb hsub Jmax Imax
    (by intro r u hr hu;simpa only [Nat.add_comm] using hcan u r hu hr)
    t j i y x hjJ hxI hyj hix
    (by rw [htarget];simpa only [Nat.add_comm] using ht)
    (by simpa only [Nat.add_comm] using hm)
  change ResidueData.BFirstStageNonexceptional D s at hnon
  exact hnon

end NS25Lean.GenericFloorDirectional
