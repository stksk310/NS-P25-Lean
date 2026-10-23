import NS25Lean.P3R3ShortStripR67
import NS25Lean.P3R3FloorR67
set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open L5A2C4C L5A2C4OR3 L5A2C4OR4 L5A2C4OR6 P3R61
variable {Gamma : NumericalSemigroup}
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "H" => routingH M.base e
local notation "Q" => principalIndex H M.base.q.val M.base.q_positive
local notation "A" => criticalExponent M.base (e 0)
local notation "B" => criticalExponent M.base (e 1)
local notation "C" => criticalExponent M.base (e 2)
local notation "P" => P3R57.roleCoefficient M hp e 0 1
local notation "T" => P3R57.roleCoefficient M hp e 0 2
local notation "U" => P3R57.roleCoefficient M hp e 1 0
local notation "V" => P3R57.roleCoefficient M hp e 1 2
local notation "W" => P3R57.roleCoefficient M hp e 2 0
local notation "Z" => P3R57.roleCoefficient M hp e 2 1

/-- NF.09 principal protection applies to every H-divisor of the protected top. -/
theorem protected_top_principal_absent (D : ℕ)
    (hprotect : (omegaDegree M hp e : ℤ)-(Q*M.base.q.val : ℕ)-D*a ∉ (H).asRelativeIdeal)
    (v : ℤ) (hdiv : (omegaDegree M hp e : ℤ)-D*a-v ∈ (H).asRelativeIdeal) :
    v-(Q*M.base.q.val : ℕ) ∉ (H).asRelativeIdeal := by
  intro hm
  apply hprotect
  have hh := ideal_add_int (H).asRelativeIdeal hdiv hm
  convert hh using 1 <;> ring

/-- A short-strip factorization forbids an F divisor after one further a-copy. -/
theorem short_strip_Z_no_F_divisor (D n i j d : ℕ) (hD0 : 0<D) (hDA : D≤A)
    (hl : RBLevel M hp e n i j d) :
    ((A:ℤ)-D)*a+Z*b-a-((i:ℤ)*b+j*c) ∉ (H).asRelativeIdeal := by
  intro hm
  obtain ⟨x,y,z,hf⟩ := routing_factorization_int M.base e _ hm
  have he : (x+1)*a+(i+y)*b+(j+z)*c=(A-D)*a+Z*b := by
    have hh := Nat.sub_add_cancel hDA
    have heZ : ((x+1:ℕ):ℤ)*a+((i+y:ℕ):ℤ)*b+((j+z:ℕ):ℤ)*c=
        ((A-D:ℕ):ℤ)*a+Z*b := by
      rw [Nat.cast_sub hDA]; push_cast at hf ⊢; nlinarith only [hf]
    exact_mod_cast heZ
  rcases short_strip_Z_factorization M hp e (A-D) (x+1) (i+y) (j+z) (by omega) he with h | h
  · have := hl.2.1; omega
  · have := hl.1; omega

/-- An RB X divisor cannot occur below the protected top when d≤D. -/
theorem short_strip_Z_no_X_divisor (D n i j d : ℕ) (hD0 : 0<D) (hDA : D≤A)
    (hl : RBLevel M hp e n i j d) (hdD : d≤D) :
    ((A:ℤ)-D)*a+Z*b-a-rbAxisA M hp e i j d ∉ (H).asRelativeIdeal := by
  intro hm
  obtain ⟨x,y,z,hf⟩ := routing_factorization_int M.base e _ hm
  have hdA : d≤A := by omega
  have hPi : P ≤ i := by have hh := hl.2.2.2.1; omega
  have he : (A-d+x+1)*a+(i-P+y)*b+z*c=(A-D)*a+Z*b := by
    have heZ : ((A-d+x+1:ℕ):ℤ)*a+((i-P+y:ℕ):ℤ)*b+(z:ℤ)*c=
        ((A-D:ℕ):ℤ)*a+Z*b := by
      rw [Nat.cast_sub hDA, Nat.cast_add, Nat.cast_add, Nat.cast_sub hdA,
        Nat.cast_add, Nat.cast_sub hPi]
      dsimp [rbAxisA] at hf
      push_cast at hf ⊢
      nlinarith only [hf]
    exact_mod_cast heZ
  rcases short_strip_Z_factorization M hp e (A-D) (A-d+x+1) (i-P+y) z (by omega) he with h | h
  · omega
  · have := hl.2.2.2.1; omega

/-- An RB Y divisor cannot occur below the protected top when d≤D. -/
theorem short_strip_Z_no_Y_divisor (D n i j d : ℕ) (hD0 : 0<D) (hDA : D≤A)
    (hl : RBLevel M hp e n i j d) (hdD : d≤D) :
    ((A:ℤ)-D)*a+Z*b-a-rbAxisB M hp e i j d ∉ (H).asRelativeIdeal := by
  intro hm
  obtain ⟨x,y,z,hf⟩ := routing_factorization_int M.base e _ hm
  have hdU : d≤U := by have := hl.2.2.2.2.2.2.2.1; omega
  have he : (U-d+x+1)*a+y*b+(j+V+z)*c=(A-D)*a+Z*b := by
    have heZ : ((U-d+x+1:ℕ):ℤ)*a+(y:ℤ)*b+((j+V+z:ℕ):ℤ)*c=
        ((A-D:ℕ):ℤ)*a+Z*b := by
      rw [Nat.cast_sub hDA, Nat.cast_add, Nat.cast_add, Nat.cast_sub hdU]
      dsimp [rbAxisB] at hf
      push_cast at hf ⊢
      nlinarith only [hf]
    exact_mod_cast heZ
  rcases short_strip_Z_factorization M hp e (A-D) (U-d+x+1) y (j+V+z) (by omega) he with h | h
  · have := hl.2.1; omega
  · have hs := (P3R58.p3_coefficient_sums M hp e).1
    omega



/-- NF.09: the protected complete short strip has no final a-predecessor. -/
theorem protected_rb_top_predecessor_absent (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, RBLevel M hp e n i j d)
    (D : ℕ) (hD0 : 0<D) (hDA : D≤A)
    (hmax : ∀ n i j d, 0<n → n<Q → RBLevel M hp e n i j d → d≤D)
    (hprotect : (omegaDegree M hp e : ℤ)-(Q*M.base.q.val : ℕ)-D*a ∉ (H).asRelativeIdeal) :
    ((A:ℤ)-D)*a+Z*b-a ∉ routingI M.base e := by
  intro hm
  rcases final_rb_membership_cover M hp e hQ hlevels _ hm with h | h
  · apply protected_top_principal_absent M hp e D hprotect _ ?_ h
    have hh := routing_combination_mem M.base e 1 0 0 (by omega) (by omega) (by omega)
    convert hh using 1 <;> dsimp [omegaDegree] <;> ring
  · obtain ⟨n,i,j,d,hn,hnQ,hl,hf | hx | hy⟩ := h
    · exact short_strip_Z_no_F_divisor M hp e D n i j d hD0 hDA hl hf
    · exact short_strip_Z_no_X_divisor M hp e D n i j d hD0 hDA hl (hmax n i j d hn hnQ hl) hx
    · exact short_strip_Z_no_Y_divisor M hp e D n i j d hD0 hDA hl (hmax n i j d hn hnQ hl) hy

/-- Divisor protection transfers the a-predecessor exclusion to both adjacent strips. -/
theorem final_predecessor_absent_of_top (s v : ℤ)
    (hstop : s-a ∉ routingI M.base e) (hdiv : s-v ∈ (H).asRelativeIdeal) :
    v-a ∉ routingI M.base e := by
  intro hm
  apply hstop
  have hh := ideal_add_int (routingI M.base e) hm hdiv
  convert hh using 1 <;> ring

/-- The three NF.09 endpoint values are actual final members, using an attained maximum. -/
theorem protected_rb_top_endpoints_mem (D n i j : ℕ) (hn : 0<n)
    (hl : RBLevel M hp e n i j D) :
    ((A:ℤ)-D)*a+(Z-1:ℕ)*b ∈ routingI M.base e ∧
    ((U:ℤ)-D)*a+(C-1:ℕ)*c ∈ routingI M.base e ∧
    ((A:ℤ)-D)*a+Z*b ∈ routingI M.base e := by
  have hs := P3R58.p3_coefficient_sums M hp e
  have hZ := P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  have hC := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  have haxes := rb_axes_mem M hp e n i j D hi0 hj0 hd0 hi hj hib hjb hd he
  have hx := return_subset_final M e n hn _ haxes.1
  have hy := return_subset_final M e n hn _ haxes.2
  have hxadd := ideal_add_int (routingI M.base e) hx
    (routing_combination_mem M.base e 0 ((Z:ℤ)-1-((i:ℤ)-P)) 0 (by omega) (by omega) (by omega))
  have hyadd := ideal_add_int (routingI M.base e) hy
    (routing_combination_mem M.base e 0 0 ((C:ℤ)-1-((j:ℤ)+V)) (by omega) (by omega) (by omega))
  have hxend : ((A:ℤ)-D)*a+(Z-1:ℕ)*b ∈ routingI M.base e := by
    convert hxadd using 1
    dsimp [rbAxisA]
    rw [Nat.cast_sub (by omega : 1≤Z)]
    push_cast
    ring
  have hyend : ((U:ℤ)-D)*a+(C-1:ℕ)*c ∈ routingI M.base e := by
    convert hyadd using 1
    dsimp [rbAxisB]
    rw [Nat.cast_sub (by omega : 1≤C)]
    push_cast
    ring
  refine ⟨hxend,hyend,?_⟩
  have hh := ideal_add_int (routingI M.base e) hxend
    (routing_combination_mem M.base e 0 1 0 (by omega) (by omega) (by omega))
  convert hh using 1
  rw [Nat.cast_sub (by omega : 1≤Z)]
  push_cast
  ring

#print axioms protected_top_principal_absent
#print axioms short_strip_Z_no_F_divisor
#print axioms short_strip_Z_no_X_divisor
#print axioms short_strip_Z_no_Y_divisor
#print axioms protected_rb_top_predecessor_absent
#print axioms final_predecessor_absent_of_top
#print axioms protected_rb_top_endpoints_mem



/-- Actual nonzero wrapped carries from four final representative equations. -/
theorem unused_merge_of_wrapped_final_representatives (x : ℤ) (D : ℕ) (hD : 0<D)
    (h0 : (routingI M.base e).aperyRepresentative a (x : ZMod a)=x)
    (hb0 : (routingI M.base e).aperyRepresentative a ((x+b:ℤ) : ZMod a)=x+b-D*a)
    (hc0 : (routingI M.base e).aperyRepresentative a ((x+c:ℤ) : ZMod a)=x+c-D*a)
    (hbc : (routingI M.base e).aperyRepresentative a ((x+b+c:ℤ) : ZMod a)=x+b+c-D*a) :
    ResidueData.ExactUnusedMergeReverseBase (routingData M.base e) (x : ZMod a) := by
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hu := (routingI M.base e).apery_step_eq a b (routingHB M.base e) (x : ZMod a)
  have hv := (routingI M.base e).apery_step_eq a c (routingHC M.base e) (x : ZMod a)
  have huc := (routingI M.base e).apery_step_eq a b (routingHB M.base e) ((x+c:ℤ) : ZMod a)
  have hvb := (routingI M.base e).apery_step_eq a c (routingHC M.base e) ((x+b:ℤ) : ZMod a)
  simp only [Int.cast_add,Int.cast_natCast] at h0 hb0 hc0 hbc huc hvb
  rw [h0,hb0] at hu
  rw [h0,hc0] at hv
  rw [hc0,show (x:ZMod a)+c+b=(x:ZMod a)+b+c by abel,hbc] at huc
  rw [hb0,hbc] at hvb
  have ha : (0:ℤ)<a := by exact_mod_cast routingA_pos M.base e
  have heu : (routingI M.base e).aperyStepQuotient a b (routingHB M.base e) (x:ZMod a)=D := by
    exact_mod_cast (show ((routingI M.base e).aperyStepQuotient a b (routingHB M.base e) (x:ZMod a):ℤ)=D by nlinarith only [hu,ha])
  have hev : (routingI M.base e).aperyStepQuotient a c (routingHC M.base e) (x:ZMod a)=D := by
    exact_mod_cast (show ((routingI M.base e).aperyStepQuotient a c (routingHC M.base e) (x:ZMod a):ℤ)=D by nlinarith only [hv,ha])
  have heuc : (routingI M.base e).aperyStepQuotient a b (routingHB M.base e) ((x:ZMod a)+c)=0 := by
    exact_mod_cast (show ((routingI M.base e).aperyStepQuotient a b (routingHB M.base e) ((x:ZMod a)+c):ℤ)=0 by nlinarith only [huc,ha])
  have hevb : (routingI M.base e).aperyStepQuotient a c (routingHC M.base e) ((x:ZMod a)+b)=0 := by
    exact_mod_cast (show ((routingI M.base e).aperyStepQuotient a c (routingHC M.base e) ((x:ZMod a)+b):ℤ)=0 by nlinarith only [hvb,ha])
  change (routingI M.base e).aperyStepQuotient a b (routingHB M.base e) (x:ZMod a)=
    (routingI M.base e).aperyStepQuotient a c (routingHC M.base e) (x:ZMod a) ∧
    0<(routingI M.base e).aperyStepQuotient a b (routingHB M.base e) (x:ZMod a) ∧
    (routingI M.base e).aperyStepQuotient a b (routingHB M.base e) ((x:ZMod a)+c)=0 ∧
    (routingI M.base e).aperyStepQuotient a c (routingHC M.base e) ((x:ZMod a)+b)=0
  exact ⟨heu.trans hev.symm,heu ▸ hD,heuc,hevb⟩



/-- NF.09 actual final protected RB corner; this is a TOTAL unused merge. -/
theorem protected_rb_corner (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, RBLevel M hp e n i j d)
    (D : ℕ)
    (hatt : ∃ n i j, 0<n ∧ n<Q ∧ RBLevel M hp e n i j D)
    (hmax : ∀ n i j d, 0<n → n<Q → RBLevel M hp e n i j d → d≤D)
    (hprotect : (omegaDegree M hp e : ℤ)-(Q*M.base.q.val : ℕ)-D*a ∉ (H).asRelativeIdeal) :
    ResidueData.ExactUnusedMergeReverseBase (routingData M.base e)
      (gridResidue M.base e (B-1) (T-1)) := by
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have haH : a ∈ H := (mem_generatedThree_iff _ _ _ _).mpr ⟨1,0,0,by simp⟩
  obtain ⟨n,i,j,hn,hnQ,hl⟩ := hatt
  have hD0 := hl.2.2.1
  have hDU := hl.2.2.2.2.2.2.2.1
  have hs := P3R58.p3_coefficient_sums M hp e
  have hr := normalized_relations M hp e
  have hZ := P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hW := P3R58.p3_coefficients_positive M hp e 2 0 (by decide)
  have hB : 0<B := by omega
  have hC : 0<C := by omega
  have hDA : D≤A := by omega
  let x : ℤ := (B-1:ℕ)*b+(T-1:ℕ)*c
  let s : ℤ := ((A:ℤ)-D)*a+Z*b
  have hOmega : x+b+c=(omegaDegree M hp e:ℤ) := by
    simp only [x,omegaDegree,Nat.cast_add,Nat.cast_mul]
    rw [Nat.cast_sub (by omega : 1≤B),Nat.cast_sub (by omega : 1≤T)]
    simp only [Nat.cast_one]
    have hsB : (B:ℤ)=P+Z := by exact_mod_cast hs.2.1
    nlinarith only [hr.1,congrArg (fun t:ℤ=>t*b) hsB]
  have hsc : s-c=((U:ℤ)-D)*a+(C-1:ℕ)*c := by
    simp only [s]
    rw [Nat.cast_sub (by omega : 1≤C)]
    simp only [Nat.cast_one]
    have hsA : (A:ℤ)=U+W := by exact_mod_cast hs.1
    nlinarith only [hr.2.2,congrArg (fun t:ℤ=>t*a) hsA]
  have hsb : s-b=((A:ℤ)-D)*a+(Z-1:ℕ)*b := by
    simp only [s]
    rw [Nat.cast_sub (by omega : 1≤Z)]
    push_cast
    ring
  have hsabs : s-a ∉ routingI M.base e :=
    protected_rb_top_predecessor_absent M hp e hQ hlevels D hD0 hDA hmax hprotect
  have hmem := protected_rb_top_endpoints_mem M hp e D n i j hn hl
  have hsmem : s ∈ routingI M.base e := hmem.2.2
  have hsbmem : s-b ∈ routingI M.base e := hsb ▸ hmem.1
  have hscmem : s-c ∈ routingI M.base e := hsc ▸ hmem.2.1
  have hsbrep : (routingI M.base e).aperyRepresentative a ((s-b:ℤ):ZMod a)=s-b := by
    apply P3R60.aperyRepresentative_eq_of_mem_not_mem_sub _ a (haH) _ hsbmem
    apply final_predecessor_absent_of_top M e s (s-b) hsabs
    convert routing_combination_mem M.base e 0 1 0 (by omega) (by omega) (by omega) using 1 <;> ring
  have hscrep : (routingI M.base e).aperyRepresentative a ((s-c:ℤ):ZMod a)=s-c := by
    apply P3R60.aperyRepresentative_eq_of_mem_not_mem_sub _ a (haH) _ hscmem
    apply final_predecessor_absent_of_top M e s (s-c) hsabs
    convert routing_combination_mem M.base e 0 0 1 (by omega) (by omega) (by omega) using 1 <;> ring
  have hsrep : (routingI M.base e).aperyRepresentative a (s:ZMod a)=s :=
    P3R60.aperyRepresentative_eq_of_mem_not_mem_sub _ a (haH) s hsmem hsabs
  have hbeta : (i:ℤ)*b+j*c ∈ routingI M.base e := by
    apply return_subset_final M e n hn
    refine ⟨by simpa using routing_combination_mem M.base e 0 i j (by omega) (by positivity) (by positivity),?_⟩
    change (i:ℤ)*b+j*c-(n*M.base.q.val:ℕ) ∈ (H).asRelativeIdeal
    rw [hl.2.2.2.2.2.2.2.2]
    convert routing_combination_mem M.base e D 0 0 (by positivity) (by omega) (by omega) using 1 <;> ring
  have hxmem : x ∈ routingI M.base e := by
    have hh := ideal_add_int (routingI M.base e) hbeta
      (routing_combination_mem M.base e 0 ((B:ℤ)-1-i) ((T:ℤ)-1-j) (by omega)
        (by have hh := hl.2.2.2.2.2.1; omega) (by have hh := hl.2.2.2.2.1; omega))
    convert hh using 1
    dsimp [x]
    rw [Nat.cast_sub (by omega : 1≤B),Nat.cast_sub (by omega : 1≤T)]
    push_cast
    ring
  have hxabs : x-a ∉ routingI M.base e := by
    intro hm
    obtain ⟨q,hq,hret⟩ := (mem_routingI_iff_positive_return M.base e _).mp hm
    apply canonical_not_positive_a M hp e (B-1) (T-1) (by omega) (by omega) (Or.inr (by omega)) 1 (by omega) (x-a) hret.1
    dsimp [x]
    ring
  have hxrep : (routingI M.base e).aperyRepresentative a (x:ZMod a)=x :=
    P3R60.aperyRepresentative_eq_of_mem_not_mem_sub _ a (haH) x hxmem hxabs
  have hsOmega : s=(omegaDegree M hp e:ℤ)-D*a := by dsimp [s,omegaDegree]; push_cast; ring
  have hmod (g:ℤ) : ((s-g:ℤ):ZMod a)=((x+b+c-g:ℤ):ZMod a) := by
    rw [hsOmega,←hOmega]
    simp only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,mul_zero,sub_zero]
  have hbmod : ((s-c:ℤ):ZMod a)=((x+b:ℤ):ZMod a) := by convert hmod c using 1 <;> ring
  have hcmod : ((s-b:ℤ):ZMod a)=((x+c:ℤ):ZMod a) := by convert hmod b using 1 <;> ring
  have hbcmod : (s:ZMod a)=((x+b+c:ℤ):ZMod a) := by simpa using hmod 0
  have hum := unused_merge_of_wrapped_final_representatives M e x D hD0 hxrep
    (by rw [←hbmod,hscrep]; rw [hsOmega,←hOmega]; ring)
    (by rw [←hcmod,hsbrep]; rw [hsOmega,←hOmega]; ring)
    (by rw [←hbcmod,hsrep]; rw [hsOmega,←hOmega])
  have hxres : (x:ZMod a)=gridResidue M.base e (B-1) (T-1) := by
    simp only [x,gridResidue,Int.cast_add,Int.cast_mul,Int.cast_natCast]

  rw [hxres] at hum
  exact hum

#print axioms unused_merge_of_wrapped_final_representatives
#print axioms protected_rb_corner






/-- An actual grid member with absent a-predecessor has exactly its displayed height. -/
theorem final_height_eq_of_predecessor_absent (n i j : ℕ)
    (hm : (normalizedGrid M.base e n i j:ℤ) ∈ routingI M.base e)
    (hprev : (normalizedGrid M.base e n i j:ℤ)-a ∉ routingI M.base e) :
    eta M.base e i j=n := by
  have hle := (normalizedGrid_mem_iff_eta_le M.base e n i j).mp hm
  by_contra hne
  have hlt : eta M.base e i j<n := by omega
  have hmem := (normalizedGrid_mem_iff_eta_le M.base e (n-1) i j).mpr (by omega)
  apply hprev
  convert hmem using 1
  simp only [normalizedGrid,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
  ring

/-- NF.09: all three exact FINAL heights on the protected RB corner strips. -/
theorem protected_rb_corner_heights (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, RBLevel M hp e n i j d)
    (D : ℕ)
    (hatt : ∃ n i j, 0<n ∧ n<Q ∧ RBLevel M hp e n i j D)
    (hmax : ∀ n i j d, 0<n → n<Q → RBLevel M hp e n i j d → d≤D)
    (hprotect : (omegaDegree M hp e : ℤ)-(Q*M.base.q.val : ℕ)-D*a ∉ (H).asRelativeIdeal) :
    eta M.base e 0 (C-1)=U-D ∧
    eta M.base e (Z-1) 0=A-D ∧
    eta M.base e Z 0=A-D := by
  obtain ⟨n,i,j,hn,hnQ,hl⟩ := hatt
  have hD0 := hl.2.2.1
  have hDU := hl.2.2.2.2.2.2.2.1
  have hs := P3R58.p3_coefficient_sums M hp e
  have hr := normalized_relations M hp e
  have hZ := P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hC : 0<C := by omega
  have hDA : D≤A := by omega
  let s : ℤ := ((A:ℤ)-D)*a+Z*b
  have hsc : s-c=((U:ℤ)-D)*a+(C-1:ℕ)*c := by
    simp only [s]
    rw [Nat.cast_sub (by omega : 1≤C)]
    simp only [Nat.cast_one]
    have hsA : (A:ℤ)=U+W := by exact_mod_cast hs.1
    nlinarith only [hr.2.2,congrArg (fun t:ℤ=>t*a) hsA]
  have hsb : s-b=((A:ℤ)-D)*a+(Z-1:ℕ)*b := by
    simp only [s]
    rw [Nat.cast_sub (by omega : 1≤Z)]
    simp only [Nat.cast_one]
    ring
  have hsabs : s-a ∉ routingI M.base e :=
    protected_rb_top_predecessor_absent M hp e hQ hlevels D hD0 hDA hmax hprotect
  have hm := protected_rb_top_endpoints_mem M hp e D n i j hn hl
  have hsbabs : s-b-a ∉ routingI M.base e := by
    apply final_predecessor_absent_of_top M e s (s-b) hsabs
    convert routing_combination_mem M.base e 0 1 0 (by omega) (by omega) (by omega) using 1 <;> ring
  have hscabs : s-c-a ∉ routingI M.base e := by
    apply final_predecessor_absent_of_top M e s (s-c) hsabs
    convert routing_combination_mem M.base e 0 0 1 (by omega) (by omega) (by omega) using 1 <;> ring
  have hcval : (normalizedGrid M.base e (U-D) 0 (C-1):ℤ)=s-c := by
    rw [hsc]
    simp only [normalizedGrid,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hDU.le,Nat.cast_zero,zero_mul,add_zero]
  have hbval : (normalizedGrid M.base e (A-D) (Z-1) 0:ℤ)=s-b := by
    rw [hsb]
    simp only [normalizedGrid,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hDA,Nat.cast_zero,zero_mul,add_zero]
  have hsval : (normalizedGrid M.base e (A-D) Z 0:ℤ)=s := by
    simp only [s,normalizedGrid,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hDA,Nat.cast_zero,zero_mul,add_zero]
  refine ⟨final_height_eq_of_predecessor_absent M e (U-D) 0 (C-1) ?_ ?_,
    final_height_eq_of_predecessor_absent M e (A-D) (Z-1) 0 ?_ ?_,
    final_height_eq_of_predecessor_absent M e (A-D) Z 0 ?_ ?_⟩
  · rw [hcval,hsc]; exact hm.2.1
  · rwa [hcval]
  · rw [hbval,hsb]; exact hm.1
  · rwa [hbval]
  · rw [hsval]; exact hm.2.2
  · rwa [hsval]
#print axioms final_height_eq_of_predecessor_absent
#print axioms protected_rb_corner_heights
end
end NS25Lean.P3R67

