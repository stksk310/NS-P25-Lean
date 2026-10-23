import NS25Lean.P3R2ZeroRectangleR63
import NS25Lean.P3R2FinalCarrierR63

set_option linter.style.header false
noncomputable section

namespace NS25Lean.P3R65
open CombinatorialCore L5A2C4I

variable {H : NumericalSemigroup} (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H)

include hb in
/-- Heights on a canonical bottom row decrease as the b-coordinate increases.
This is a statement about the final ideal's actual Apéry representatives. -/
theorem bottom_height_antitone
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (i j : ℕ) (hij : i ≤ j)
    (hcanI : H.asRelativeIdeal.aperyRepresentative a ((i*b : ℕ) : ZMod a) =
      (i*b : ℕ))
    (hcanJ : H.asRelativeIdeal.aperyRepresentative a ((j*b : ℕ) : ZMod a) =
      (j*b : ℕ)) :
    P3R61.idealHeight I a hsub ((j*b : ℕ) : ZMod a) ≤
      P3R61.idealHeight I a hsub ((i*b : ℕ) : ZMod a) := by
  let n := P3R61.idealHeight I a hsub ((i*b : ℕ) : ZMod a)
  have he := P3R61.idealHeight_eq I a hsub ((i*b : ℕ) : ZMod a)
  rw [hcanI] at he
  have hmem : ((i*b : ℕ) : ℤ)+(a : ℤ)*n ∈ I := by
    simpa only [n, ← he] using I.aperyRepresentative_mem a ((i*b : ℕ) : ZMod a)
  have hdiff : (j-i)*b ∈ H := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using H.toAddSubmonoid.nsmul_mem hb (j-i)
  have hm : ((j*b : ℕ) : ℤ)+(a : ℤ)*n ∈ I := by
    have hm := I.add_mem_nat hmem hdiff
    convert hm using 1 <;> push_cast <;>
      nlinarith [Nat.sub_add_cancel hij]
  simpa only [Int.cast_natCast, n] using P3R61.canonical_height_le I a hsub (j*b : ℕ) n
    (by simpa only [Int.cast_natCast] using hcanJ) hm

/-- A canonical, height-zero upper seed whose c-edge wraps with carry W
forces the precise W-to-below-W bottom crossing. -/
theorem x_crossing_of_wrap
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (s : ResidueData.CSourceTargetBranches (P3R60.idealData I a b c hb hc))
    (x : ℤ) (i W : ℕ) (hi : 0 < i)
    (hs : s.val = (x : ZMod a))
    (hcan : H.asRelativeIdeal.aperyRepresentative a (x : ZMod a) = x)
    (hx : x ∈ I)
    (hwrap : x+c = ((i-1)*b : ℕ)+(a : ℤ)*W)
    (hcanPrev : H.asRelativeIdeal.aperyRepresentative a (((i-1)*b : ℕ) : ZMod a) =
      ((i-1)*b : ℕ))
    (hcanNext : H.asRelativeIdeal.aperyRepresentative a ((i*b : ℕ) : ZMod a) =
      (i*b : ℕ)) :
    P3R61.idealHeight I a hsub (((i-1)*b : ℕ) : ZMod a) = W ∧
      P3R61.idealHeight I a hsub ((i*b : ℕ) : ZMod a) < W := by
  let D := P3R60.idealData I a b c hb hc
  have ha : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have hseed : I.aperyRepresentative a (x : ZMod a) = x := by
    apply le_antisymm (I.aperyRepresentative_le a _ hx rfl)
    have hl := H.asRelativeIdeal.aperyRepresentative_le a _
      (hsub _ (I.aperyRepresentative_mem a (x : ZMod a)))
      (I.aperyRepresentative_mod a (x : ZMod a))
    rwa [hcan] at hl
  have hv := s.property.1.2
  change I.aperyStepQuotient a c hc s.val = 0 at hv
  rw [hs] at hv
  have hcEq := I.apery_step_eq a c hc (x : ZMod a)
  rw [hseed,hv] at hcEq
  simp only [Nat.cast_zero,mul_zero,add_zero] at hcEq
  have hprevMod : (x : ZMod a)+c = (((i-1)*b : ℕ) : ZMod a) := by
    have he := congrArg (fun z : ℤ => (z : ZMod a)) hwrap
    simpa using he
  have hprev := P3R61.idealHeight_eq I a hsub (((i-1)*b : ℕ) : ZMod a)
  rw [hcanPrev] at hprev
  have hprevRep : I.aperyRepresentative a (((i-1)*b : ℕ) : ZMod a) =
      ((i-1)*b : ℕ)+(a : ℤ)*W := by
    rw [← hprevMod]
    exact hcEq.symm.trans hwrap
  have hheight : P3R61.idealHeight I a hsub (((i-1)*b : ℕ) : ZMod a) = W := by
    have he : (P3R61.idealHeight I a hsub (((i-1)*b : ℕ) : ZMod a) : ℤ) = W := by
      rw [hprevRep] at hprev
      nlinarith
    exact_mod_cast he
  refine ⟨hheight, ?_⟩
  have hcross := (ResidueData.sourceTargetBranch_iff_positive_cross D).mp s.property |>.2.2
  change 0 < I.aperyStepQuotient a b hb (s.val+c) at hcross
  rw [hs,hprevMod] at hcross
  have hbEq := I.apery_step_eq a b hb (((i-1)*b : ℕ) : ZMod a)
  have hnextMod : (((i-1)*b : ℕ) : ZMod a)+b = ((i*b : ℕ) : ZMod a) := by
    have he := congrArg (fun k : ℕ => (k : ZMod a))
      (show (i-1)*b+b=i*b by nlinarith [Nat.sub_add_cancel (show 1 ≤ i by omega)])
    simpa only [Nat.cast_add] using he
  rw [hprevRep,hnextMod] at hbEq
  have hnext := P3R61.idealHeight_eq I a hsub ((i*b : ℕ) : ZMod a)
  rw [hcanNext] at hnext
  rw [hnext] at hbEq
  have hcpos : (0 : ℤ) < I.aperyStepQuotient a b hb (((i-1)*b : ℕ) : ZMod a) := by
    exact_mod_cast hcross
  have hiEq : ((i-1)*b : ℕ)+b=i*b := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ i by omega)]
  have hiInt : (((i-1)*b : ℕ) : ℤ)+b=((i*b : ℕ) : ℤ) := by exact_mod_cast hiEq
  have hlt : (P3R61.idealHeight I a hsub ((i*b : ℕ) : ZMod a) : ℤ) < W := by
    nlinarith only [hbEq, hiInt, ha, mul_pos ha hcpos]
  exact_mod_cast hlt

/-- The actual coherent c-wrap fixes the upper seed and gives its bottom
crossing. Membership and canonicality are required only for displayed cells. -/
theorem x_crossing_of_upper_grid
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (s : ResidueData.CSourceTargetBranches (P3R60.idealData I a b c hb hc))
    (i Z C W : ℕ) (hi : 0 < i) (hC : 0 < C)
    (hrel : (C : ℤ)*c=(a : ℤ)*W+(Z : ℤ)*b)
    (ht : (P3R60.idealData I a b c hb hc).branchTarget s.val =
      (((Z+i)*b : ℕ) : ZMod a))
    (hcan : H.asRelativeIdeal.aperyRepresentative a
      ((((i-1)*b+(C-1)*c : ℕ) : ℤ) : ZMod a) = ((i-1)*b+(C-1)*c : ℕ))
    (hx : (((i-1)*b+(C-1)*c : ℕ) : ℤ) ∈ I)
    (hcanPrev : H.asRelativeIdeal.aperyRepresentative a
      (((Z+i-1)*b : ℕ) : ZMod a) = ((Z+i-1)*b : ℕ))
    (hcanNext : H.asRelativeIdeal.aperyRepresentative a
      (((Z+i)*b : ℕ) : ZMod a) = ((Z+i)*b : ℕ)) :
    P3R61.idealHeight I a hsub (((Z+i-1)*b : ℕ) : ZMod a) = W ∧
      P3R61.idealHeight I a hsub (((Z+i)*b : ℕ) : ZMod a) < W := by
  let x : ℤ := ((i-1)*b+(C-1)*c : ℕ)
  have hiSub : (i-1 : ℕ)+1=i := by omega
  have hCSub : (C-1 : ℕ)+1=C := by omega
  have hISub : (Z+i-1 : ℕ)=Z+(i-1) := by omega
  have hwrap : x+c=((Z+i-1)*b : ℕ)+(a : ℤ)*W := by
    dsimp [x]
    push_cast
    have hiInt := congrArg (fun n : ℕ => (n : ℤ)) hiSub
    have hCInt := congrArg (fun n : ℕ => (n : ℤ)) hCSub
    have hIInt := congrArg (fun n : ℕ => (n : ℤ)) hISub
    push_cast at hiInt hCInt hIInt
    nlinarith only [hrel, hiInt, hCInt, hIInt]
  have hs : s.val=(x : ZMod a) := by
    have hm := congrArg (fun z : ℤ => (z : ZMod a)) hwrap
    have hcoord : (((Z+i-1)*b : ℕ) : ZMod a)+b=(((Z+i)*b : ℕ) : ZMod a) := by
      have he := congrArg (fun n : ℕ => (n : ZMod a))
        (show (Z+i-1)*b+b=(Z+i)*b by nlinarith [Nat.sub_add_cancel (show 1 ≤ Z+i by omega)])
      simpa only [Nat.cast_add] using he
    have htm : s.val+b+c=(((Z+i)*b : ℕ) : ZMod a) := ht
    have hwm : (x : ZMod a)+c=(((Z+i-1)*b : ℕ) : ZMod a) := by simpa using hm
    linear_combination htm-hcoord-hwm
  exact x_crossing_of_wrap I a b c hb hc hsub s x (Z+i) W (by omega)
    hs hcan hx hwrap hcanPrev hcanNext

/-- Only one branch can cross the same bottom height. The coordinate index
need not identify a return witness, and no candidate minimality is assumed. -/
theorem cExceptionalCount_le_one_of_bottom_crossings
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (B W : ℕ)
    (hcan : ∀ i : ℕ, i < B →
      H.asRelativeIdeal.aperyRepresentative a ((i*b : ℕ) : ZMod a) = (i*b : ℕ))
    (hcross : ∀ s : ResidueData.CExceptionalBranches (P3R60.idealData I a b c hb hc),
      ∃ i : ℕ, 0 < i ∧ i < B ∧
        (P3R60.idealData I a b c hb hc).branchTarget s.val.val = ((i*b : ℕ) : ZMod a) ∧
        P3R61.idealHeight I a hsub (((i-1)*b : ℕ) : ZMod a) = W ∧
        P3R61.idealHeight I a hsub ((i*b : ℕ) : ZMod a) < W) :
    ResidueData.cExceptionalCount (P3R60.idealData I a b c hb hc) ≤ 1 := by
  let D := P3R60.idealData I a b c hb hc
  have hunique : Subsingleton (ResidueData.CExceptionalBranches D) := by
    constructor
    intro s t
    obtain ⟨i,hi,hiB,hs,hprevI,hnextI⟩ := hcross s
    obtain ⟨j,hj,hjB,ht,hprevJ,hnextJ⟩ := hcross t
    have he : i=j := by
      rcases lt_trichotomy i j with hij | he | hji
      · have hm := bottom_height_antitone I a b hb hsub i (j-1) (by omega)
          (hcan i hiB) (hcan (j-1) (by omega))
        rw [hprevJ] at hm
        omega
      · exact he
      · have hm := bottom_height_antitone I a b hb hsub j (i-1) (by omega)
          (hcan j hjB) (hcan (i-1) (by omega))
        rw [hprevI] at hm
        omega
    have htarget : D.branchTarget s.val.val = D.branchTarget t.val.val := by
      rw [hs,ht,he]
    exact Subtype.ext (Subtype.ext (D.branchTarget_injective htarget))
  have hinj : Function.Injective (fun _ : ResidueData.CExceptionalBranches D => ()) :=
    fun s t _ => hunique.elim s t
  exact le_trans (Nat.card_le_card_of_injective _ hinj) (by simp)

end NS25Lean.P3R65

namespace NS25Lean.P3R65
open CombinatorialCore L5A2C4I ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H

variable {Gamma : NumericalSemigroup}

/-- A final X target in the same coherent role has the unique bottom crossing.
The upper row is zero because the actual final ideal contains the principal kc. -/
theorem routing_x_target_crossing (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n i j d k : ℕ) (hl : P3R61.LTLevel M hp e n i j d)
    (hk : k < criticalExponent M.base (e 2))
    (hprincipal : ((k*routingC M.base e : ℕ) : ℤ) ∈ routingI M.base e)
    (s : ResidueData.CSourceTargetBranches (routingData M.base e))
    (ht : (routingI M.base e).aperyRepresentative (routingA M.base e)
      ((routingData M.base e).branchTarget s.val) = P3R61.ltAxisA M hp e i j d) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let hsub := P3R63.routing_ideal_subset M.base e
    let Z := P3R57.roleCoefficient M hp e 2 1
    let W := P3R57.roleCoefficient M hp e 2 0
    P3R61.idealHeight (routingI M.base e) (routingA M.base e) hsub
      (((Z+i-1)*routingB M.base e : ℕ) : ZMod (routingA M.base e)) = W ∧
    P3R61.idealHeight (routingI M.base e) (routingA M.base e) hsub
      (((Z+i)*routingB M.base e : ℕ) : ZMod (routingA M.base e)) < W := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  let a := routingA M.base e
  let b := routingB M.base e
  let c := routingC M.base e
  let C := criticalExponent M.base (e 2)
  let Z := P3R57.roleCoefficient M hp e 2 1
  let W := P3R57.roleCoefficient M hp e 2 0
  rcases hl with ⟨hi,hj,hd,hiP,hTj,hiB,hjC,hdW,hreturn⟩
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hC : 0 < C := by dsimp [C]; omega
  have hI : Z+i < criticalExponent M.base (e 1) := by dsimp [Z]; omega
  have hIprev : Z+i-1 < criticalExponent M.base (e 1) := by omega
  have hT : 0 < P3R57.roleCoefficient M hp e 0 2 :=
    P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hcanUpper := P3R60.canonical_grid_value M.base e (i-1) (C-1)
    (P3R58.p3_lshape_canonical M hp e (i-1) (C-1) (by omega)
      (by omega) (Or.inl (by omega)))
  have hcanPrev := P3R60.canonical_grid_value M.base e (Z+i-1) 0
    (P3R58.p3_lshape_canonical M hp e (Z+i-1) 0 hIprev (by omega)
      (Or.inr hT))
  have hcanNext := P3R60.canonical_grid_value M.base e (Z+i) 0
    (P3R58.p3_lshape_canonical M hp e (Z+i) 0 hI (by omega)
      (Or.inr hT))
  have hmemUpper : ((((i-1)*b+(C-1)*c : ℕ) : ℤ)) ∈ routingI M.base e := by
    apply P3R63.grid_mem_of_le (routingI M.base e) b c (routingHB M.base e)
      (routingHC M.base e) 0 k (i-1) (C-1) (by omega) (by dsimp [C]; omega)
    simpa only [zero_mul,zero_add] using hprincipal
  have htarget : (routingData M.base e).branchTarget s.val = (((Z+i)*b : ℕ) : ZMod a) := by
    have he := (routingI M.base e).aperyRepresentative_mod a
      ((routingData M.base e).branchTarget s.val)
    rw [ht] at he
    symm
    have he' : (((((W : ℤ)-d)*a+((i : ℤ)+Z)*b : ℤ)) : ZMod a) =
        (routingData M.base e).branchTarget s.val := by
      simpa only [P3R61.ltAxisA,zero_mul,add_zero] using he
    have haZero : (a : ZMod a)=0 := ZMod.natCast_self a
    simp only [Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_natCast,
      haZero,mul_zero,zero_add] at he'
    simpa only [Nat.cast_mul,Nat.cast_add,add_comm] using he'
  apply x_crossing_of_upper_grid (routingI M.base e) a b c (routingHB M.base e)
    (routingHC M.base e) (P3R63.routing_ideal_subset M.base e) s i Z C W hi hC
      (by simpa [a,b,c,C,Z,W, mul_comm] using (P3R61.normalized_relations M hp e).2.2)
      htarget _ hmemUpper _ _
  · simpa only [P3R60.CanonicalValue,L5A2C4OR3.physicalAlpha,Nat.cast_add,Nat.cast_mul]
      using hcanUpper
  · simpa only [P3R60.CanonicalValue,L5A2C4OR3.physicalAlpha,Nat.cast_add,Nat.cast_mul,
      Nat.cast_zero,zero_mul,add_zero,Int.cast_add,Int.cast_mul,Int.cast_natCast]
      using hcanPrev
  · simpa only [P3R60.CanonicalValue,L5A2C4OR3.physicalAlpha,Nat.cast_add,Nat.cast_mul,
      Nat.cast_zero,zero_mul,add_zero,Int.cast_add,Int.cast_mul,Int.cast_natCast]
      using hcanNext

end NS25Lean.P3R65

namespace NS25Lean.P3R65
open CombinatorialCore L5A2C4I ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H
variable {Gamma : NumericalSemigroup}

/-- Geometry-only assembly: if every final exceptional target is an LT X
candidate, all exceptional branches cross one bottom height and coincide. -/
theorem routing_cExceptional_le_one_of_x_targets (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (k : ℕ)
    (hk : k < criticalExponent M.base (e 2))
    (hprincipal : ((k*routingC M.base e : ℕ) : ℤ) ∈ routingI M.base e)
    (htargets : ∀ s : ResidueData.CExceptionalBranches (routingData M.base e),
      ∃ n i j d : ℕ, P3R61.LTLevel M hp e n i j d ∧
        (routingI M.base e).aperyRepresentative (routingA M.base e)
          ((routingData M.base e).branchTarget s.val.val) = P3R61.ltAxisA M hp e i j d) :
    ResidueData.cExceptionalCount (routingData M.base e) ≤ 1 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  let a := routingA M.base e
  let b := routingB M.base e
  let c := routingC M.base e
  let Z := P3R57.roleCoefficient M hp e 2 1
  let W := P3R57.roleCoefficient M hp e 2 0
  let B := criticalExponent M.base (e 1)
  have hT : 0 < P3R57.roleCoefficient M hp e 0 2 :=
    P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  apply cExceptionalCount_le_one_of_bottom_crossings (routingI M.base e) a b c
    (routingHB M.base e) (routingHC M.base e) (P3R63.routing_ideal_subset M.base e) B W
  · intro i hi
    have hC := (criticalExponent_spec M.base (e 2)).1
    have hcan := P3R60.canonical_grid_value M.base e i 0
      (P3R58.p3_lshape_canonical M hp e i 0 hi (by omega) (Or.inr hT))
    simpa only [P3R60.CanonicalValue,L5A2C4OR3.physicalAlpha,Nat.cast_zero,zero_mul,add_zero,
      Nat.cast_mul,Int.cast_mul,Int.cast_natCast] using hcan
  · intro s
    obtain ⟨n,i,j,d,hl,ht⟩ := htargets s
    have hcross := routing_x_target_crossing M hp e n i j d k hl hk hprincipal s.val ht
    have hsum := P3R58.p3_coefficient_sums M hp e
    have hi : 0 < Z+i := by have hh := hl.1; omega
    have hiB : Z+i < B := by have hh := hl.2.2.2.1; dsimp [Z,B]; omega
    refine ⟨Z+i,hi,hiB,?_,hcross.1,hcross.2⟩
    have he := (routingI M.base e).aperyRepresentative_mod a
      ((routingData M.base e).branchTarget s.val.val)
    rw [ht] at he
    change s.val.val+b+c=(((Z+i)*b : ℕ) : ZMod a)
    symm
    have he' : (((((W : ℤ)-d)*a+((i : ℤ)+Z)*b : ℤ)) : ZMod a) =
        (routingData M.base e).branchTarget s.val.val := by
      simpa only [P3R61.ltAxisA,zero_mul,add_zero] using he
    have haZero : (a : ZMod a)=0 := ZMod.natCast_self a
    simp only [Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_natCast,
      haZero,mul_zero,zero_add] at he'
    change ((i : ZMod a)+Z)*b=s.val.val+b+c at he'
    simpa only [Nat.cast_mul,Nat.cast_add,add_comm] using he'

end NS25Lean.P3R65
