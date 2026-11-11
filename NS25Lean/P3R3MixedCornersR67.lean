import NS25Lean.P3R3CornersR67
import NS25Lean.P3R3PrincipalR67
import NS25Lean.P3R1ReturnGeometryR64
set_option linter.style.header false
set_option autoImplicit false
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

/-- A full-support principal cannot divide any protected RB short-strip top. -/
theorem fullsupport_rb_protection (hfull : PrincipalFullSupport M e) (D : ℕ) :
    (omegaDegree M hp e:ℤ)-(Q*M.base.q.val:ℕ)-D*a ∉ (H).asRelativeIdeal := by
  intro hm
  obtain ⟨L,I,J,hL,hI,hJ,hf⟩ := hfull
  obtain ⟨r,s,t,hr⟩ := routing_factorization_int M.base e _ hm
  have heZ : ((L+r+D:ℕ):ℤ)*a+((I+s:ℕ):ℤ)*b+((J+t:ℕ):ℤ)*c=(omegaDegree M hp e:ℤ) := by
    have hfZ : (Q*M.base.q.val:ℕ)=(L:ℤ)*a+I*b+J*c := by exact_mod_cast hf
    simp only [Nat.cast_add]
    nlinarith only [hr,hfZ]
  have he : (L+r+D)*a+(I+s)*b+(J+t)*c=omegaDegree M hp e := by exact_mod_cast heZ
  rcases omega_factorization_table M hp e _ _ _ he with h | h | h <;> omega

/-- An LT F cannot divide any RB short strip, since both transverse axes occur. -/
theorem rb_strip_no_LT_F_divisor (D n i j d : ℕ) (hD0 : 0<D) (hDA : D≤A)
    (hl : LTLevel M hp e n i j d) :
    ((A:ℤ)-D)*a+Z*b-a-((i:ℤ)*b+j*c) ∉ (H).asRelativeIdeal := by
  intro hm
  obtain ⟨x,y,z,hf⟩ := routing_factorization_int M.base e _ hm
  have heZ : ((x+1:ℕ):ℤ)*a+((i+y:ℕ):ℤ)*b+((j+z:ℕ):ℤ)*c=((A-D:ℕ):ℤ)*a+Z*b := by
    rw [Nat.cast_sub hDA]
    push_cast at hf ⊢
    nlinarith only [hf]
  have he : (x+1)*a+(i+y)*b+(j+z)*c=(A-D)*a+Z*b := by exact_mod_cast heZ
  rcases short_strip_Z_factorization M hp e (A-D) (x+1) (i+y) (j+z) (by omega) he with h | h
  · have hh := hl.2.1; omega
  · have hh := hl.1; omega

/-- LT X has too many b-copies to divide either complete RB strip factorization. -/
theorem rb_strip_no_LT_X_divisor (D n i j d : ℕ) (hD0 : 0<D) (hDA : D≤A)
    (hl : LTLevel M hp e n i j d) :
    ((A:ℤ)-D)*a+Z*b-a-ltAxisA M hp e i j d ∉ (H).asRelativeIdeal := by
  intro hm
  obtain ⟨x,y,z,hf⟩ := routing_factorization_int M.base e _ hm
  have hdW : d≤W := by have hh := hl.2.2.2.2.2.2.2.1; omega
  have heZ : ((W-d+x+1:ℕ):ℤ)*a+((i+Z+y:ℕ):ℤ)*b+(z:ℤ)*c=((A-D:ℕ):ℤ)*a+Z*b := by
    rw [Nat.cast_sub hDA,Nat.cast_add,Nat.cast_add,Nat.cast_sub hdW]
    simp only [ltAxisA] at hf
    push_cast at hf ⊢
    nlinarith only [hf]
  have he : (W-d+x+1)*a+(i+Z+y)*b+z*c=(A-D)*a+Z*b := by exact_mod_cast heZ
  rcases short_strip_Z_factorization M hp e (A-D) (W-d+x+1) (i+Z+y) z (by omega) he with h | h <;>
    have hh := hl.1 <;> omega

/-- LT Y has too many a-copies for the second RB strip representation. -/
theorem rb_strip_no_LT_Y_divisor (D n i j d : ℕ) (hD0 : 0<D) (hDA : D≤A)
    (hl : LTLevel M hp e n i j d) :
    ((A:ℤ)-D)*a+Z*b-a-ltAxisB M hp e i j d ∉ (H).asRelativeIdeal := by
  intro hm
  obtain ⟨x,y,z,hf⟩ := routing_factorization_int M.base e _ hm
  have hs := P3R58.p3_coefficient_sums M hp e
  have hdW : d<W := hl.2.2.2.2.2.2.2.1
  have hdA : d≤A := by omega
  have hTj : T≤j := by have hh := hl.2.2.2.2.1; omega
  have heZ : ((A-d+x+1:ℕ):ℤ)*a+(y:ℤ)*b+((j-T+z:ℕ):ℤ)*c=((A-D:ℕ):ℤ)*a+Z*b := by
    rw [Nat.cast_sub hDA,Nat.cast_add,Nat.cast_add,Nat.cast_sub hdA,Nat.cast_add,Nat.cast_sub hTj]
    simp only [ltAxisB] at hf
    push_cast at hf ⊢
    nlinarith only [hf]
  have he : (A-d+x+1)*a+y*b+(j-T+z)*c=(A-D)*a+Z*b := by exact_mod_cast heZ
  rcases short_strip_Z_factorization M hp e (A-D) (A-d+x+1) y (j-T+z) (by omega) he with h | h
  · have hh := hl.2.2.2.2.1; omega
  · omega

/-- Mixed-arm NF/TW top protection uses the actual final mixed generator cover. -/
theorem shared_protected_rb_top_predecessor_absent
    (hR3 : (P3R51.internalDegrees M).card=3)
    (D : ℕ) (hD0 : 0<D) (hDA : D≤A)
    (hmax : ∀ n i j d, 0<n → n<Q → RBLevel M hp e n i j d → d≤D)
    (hprotect : (omegaDegree M hp e:ℤ)-(Q*M.base.q.val:ℕ)-D*a ∉ (H).asRelativeIdeal) :
    ((A:ℤ)-D)*a+Z*b-a ∉ routingI M.base e := by
  intro hm
  rcases final_r3_membership_cover M hp hR3 e _ hm with h | h
  · apply protected_top_principal_absent M hp e D hprotect _ ?_ h
    convert routing_combination_mem M.base e 1 0 0 (by omega) (by omega) (by omega) using 1 <;>
      simp only [omegaDegree,Nat.cast_add,Nat.cast_mul] <;> ring
  · obtain ⟨n,i,j,d,hn,hnQ,(⟨hl,hf | hx | hy⟩ | ⟨hl,hf | hx | hy⟩)⟩ := h
    · exact short_strip_Z_no_F_divisor M hp e D n i j d hD0 hDA hl hf
    · exact short_strip_Z_no_X_divisor M hp e D n i j d hD0 hDA hl (hmax n i j d hn hnQ hl) hx
    · exact short_strip_Z_no_Y_divisor M hp e D n i j d hD0 hDA hl (hmax n i j d hn hnQ hl) hy
    · exact rb_strip_no_LT_F_divisor M hp e D n i j d hD0 hDA hl hf
    · exact rb_strip_no_LT_X_divisor M hp e D n i j d hD0 hDA hl hx
    · exact rb_strip_no_LT_Y_divisor M hp e D n i j d hD0 hDA hl hy
theorem mixed_rb_top_predecessor_absent
    (hR3 : (P3R51.internalDegrees M).card=3) (hfull : PrincipalFullSupport M e)
    (D : ℕ) (hD0 : 0<D) (hDA : D≤A)
    (hmax : ∀ n i j d, 0<n → n<Q → RBLevel M hp e n i j d → d≤D) :
    ((A:ℤ)-D)*a+Z*b-a ∉ routingI M.base e := by
  exact shared_protected_rb_top_predecessor_absent M hp e hR3 D hD0 hDA hmax
    (fullsupport_rb_protection M hp e hfull D)

/-- NF.09 actual final protected RB corner; this is a TOTAL unused merge. -/
theorem shared_protected_rb_corner (hR3 : (P3R51.internalDegrees M).card=3)
    (D : ℕ)
    (hatt : ∃ n i j, 0<n ∧ n<Q ∧ RBLevel M hp e n i j D)
    (hmax : ∀ n i j d, 0<n → n<Q → RBLevel M hp e n i j d → d≤D)
    (hprotect : (omegaDegree M hp e:ℤ)-(Q*M.base.q.val:ℕ)-D*a ∉ (H).asRelativeIdeal) :
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
    shared_protected_rb_top_predecessor_absent M hp e hR3 D hD0 hDA hmax hprotect
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


/-- Exact protected heights from the same shared both-arm top exclusion. -/
theorem shared_protected_rb_corner_heights
    (hR3 : (P3R51.internalDegrees M).card=3)
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
    shared_protected_rb_top_predecessor_absent M hp e hR3 D hD0 hDA hmax hprotect
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

theorem mixed_rb_corner (hR3 : (P3R51.internalDegrees M).card=3) (hfull : PrincipalFullSupport M e)
    (D : ℕ)
    (hatt : ∃ n i j, 0<n ∧ n<Q ∧ RBLevel M hp e n i j D)
    (hmax : ∀ n i j d, 0<n → n<Q → RBLevel M hp e n i j d → d≤D)
    :
    ResidueData.ExactUnusedMergeReverseBase (routingData M.base e)
      (gridResidue M.base e (B-1) (T-1)) := by
  exact shared_protected_rb_corner M hp e hR3 D hatt hmax
    (fullsupport_rb_protection M hp e hfull D)


#print axioms fullsupport_rb_protection
#print axioms rb_strip_no_LT_F_divisor
#print axioms rb_strip_no_LT_X_divisor
#print axioms rb_strip_no_LT_Y_divisor
#print axioms mixed_rb_top_predecessor_absent
#print axioms mixed_rb_corner



/-- Carrier-congruent concrete data exchange directions without changing unused merges. -/
theorem concrete_unused_merge_swap {K K' : NumericalSemigroup}
    (I : RelativeIdeal K) (I' : RelativeIdeal K')
    (aa aa' bb cc bb' cc' : ℕ) [NeZero aa] [NeZero aa']
    (hb : bb∈K) (hc : cc∈K) (hb' : bb'∈K') (hc' : cc'∈K')
    (ha : aa'=aa) (hbs : bb'=cc) (hcs : cc'=bb) (hI : I'.carrier=I.carrier) (x : ℤ) :
    ResidueData.ExactUnusedMergeReverseBase (P3R60.idealData I' aa' bb' cc' hb' hc') (x:ZMod aa') ↔
    ResidueData.ExactUnusedMergeReverseBase (P3R60.idealData I aa bb cc hb hc) (x:ZMod aa) := by
  subst aa'; subst bb'; subst cc'
  change (I'.aperyStepQuotient aa cc hb' (x:ZMod aa)=I'.aperyStepQuotient aa bb hc' (x:ZMod aa) ∧
    0<I'.aperyStepQuotient aa cc hb' (x:ZMod aa) ∧
    I'.aperyStepQuotient aa cc hb' ((x:ZMod aa)+bb)=0 ∧ I'.aperyStepQuotient aa bb hc' ((x:ZMod aa)+cc)=0) ↔
    (I.aperyStepQuotient aa bb hb (x:ZMod aa)=I.aperyStepQuotient aa cc hc (x:ZMod aa) ∧
    0<I.aperyStepQuotient aa bb hb (x:ZMod aa) ∧
    I.aperyStepQuotient aa bb hb ((x:ZMod aa)+cc)=0 ∧ I.aperyStepQuotient aa cc hc ((x:ZMod aa)+bb)=0)
  rw [P3R57.aperyStepQuotient_carrier_congr I I' aa cc hc hb' hI,
    P3R57.aperyStepQuotient_carrier_congr I I' aa bb hb hc' hI]
  omega

/-- The actual b/c role exchange preserves TOTAL exact unused merge bases. -/
theorem actual_unused_merge_swap_iff (x : ℤ) :
    ResidueData.ExactUnusedMergeReverseBase (routingData M.base (P3R57.swapRole e))
      (x:ZMod (routingA M.base (P3R57.swapRole e))) ↔
    ResidueData.ExactUnusedMergeReverseBase (routingData M.base e) (x:ZMod a) := by
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  letI : NeZero (routingA M.base (P3R57.swapRole e)) := ⟨Nat.ne_of_gt (routingA_pos M.base (P3R57.swapRole e))⟩
  exact concrete_unused_merge_swap (routingI M.base e) (routingI M.base (P3R57.swapRole e))
    a (routingA M.base (P3R57.swapRole e)) b c (routingB M.base (P3R57.swapRole e)) (routingC M.base (P3R57.swapRole e))
    (routingHB M.base e) (routingHC M.base e) (routingHB M.base (P3R57.swapRole e)) (routingHC M.base (P3R57.swapRole e))
    (P3R57.routingA_swap M.base e) (P3R57.routingB_swap M.base e) (P3R57.routingC_swap M.base e)
    (P3R57.routingI_carrier_swap M.base e) x
/-- Actual strict-arm coordinates exchange under the actual b/c role permutation. -/
theorem rb_swap_iff_lt (n i j d : ℕ) :
    RBLevel M hp (P3R57.swapRole e) n j i d ↔ LTLevel M hp e n i j d := by
  simp only [RBLevel,LTLevel,P3R57.routingA_swap,P3R57.routingB_swap,P3R57.routingC_swap,
    P3R57.swapRole_one,P3R57.swapRole_two,P3R57.roleCoefficient_swap]
  norm_num [Equiv.swap_apply_def]
  constructor <;> rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ <;>
    exact ⟨h2,h1,h3,h5,h4,h7,h6,h8,by linarith only [h9]⟩

/-- Full support is retained by the actual b/c role exchange. -/
theorem fullsupport_swap (hfull : PrincipalFullSupport M e) :
    PrincipalFullSupport M (P3R57.swapRole e) := by
  obtain ⟨L,I,J,hL,hI,hJ,he⟩ := hfull
  refine ⟨L,J,I,hL,hJ,hI,?_⟩
  simpa only [P3R64.routingH_swapBC,P3R57.routingA_swap,P3R57.routingB_swap,P3R57.routingC_swap,
    add_comm,add_left_comm,add_assoc] using he

/-- TW.08: the occupied LT corner is a TOTAL exact unused merge in the same final graph. -/
theorem shared_protected_lt_corner (hR3 : (P3R51.internalDegrees M).card=3)
    (D : ℕ)
    (hatt : ∃ n i j, 0<n ∧ n<Q ∧ LTLevel M hp e n i j D)
    (hmax : ∀ n i j d, 0<n → n<Q → LTLevel M hp e n i j d → d≤D)
    (hprotect : (omegaDegree M hp (P3R57.swapRole e):ℤ)-(Q*M.base.q.val:ℕ)-D*a ∉ (H).asRelativeIdeal) :
    ResidueData.ExactUnusedMergeReverseBase (routingData M.base e)
      (gridResidue M.base e (P-1) (C-1)) := by
  have hatt' : ∃ n i j, 0<n ∧
      n<principalIndex (routingH M.base (P3R57.swapRole e)) M.base.q.val M.base.q_positive ∧
      RBLevel M hp (P3R57.swapRole e) n i j D := by
    obtain ⟨n,i,j,hn,hnQ,hl⟩ := hatt
    refine ⟨n,j,i,hn,?_,(rb_swap_iff_lt M hp e n i j D).mpr hl⟩
    simpa only [P3R64.routingH_swapBC] using hnQ
  have hmax' : ∀ n i j d, 0<n →
      n<principalIndex (routingH M.base (P3R57.swapRole e)) M.base.q.val M.base.q_positive →
      RBLevel M hp (P3R57.swapRole e) n i j d → d≤D := by
    intro n i j d hn hnQ hl
    apply hmax n j i d hn (by simpa only [P3R64.routingH_swapBC] using hnQ)
    exact (rb_swap_iff_lt M hp e n j i d).mp hl
  have hprotect' : (omegaDegree M hp (P3R57.swapRole e):ℤ)-
      (principalIndex (routingH M.base (P3R57.swapRole e)) M.base.q.val M.base.q_positive*M.base.q.val:ℕ)-
      D*routingA M.base (P3R57.swapRole e) ∉ (routingH M.base (P3R57.swapRole e)).asRelativeIdeal := by
    rw [P3R64.routingH_swapBC M.base e, P3R57.routingA_swap M.base e]
    exact hprotect
  have hcorner := shared_protected_rb_corner M hp (P3R57.swapRole e) hR3 D hatt' hmax' hprotect'
  let x : ℤ := (P-1:ℕ)*b+(C-1:ℕ)*c
  have hgrid' : gridResidue M.base (P3R57.swapRole e)
      (criticalExponent M.base (P3R57.swapRole e 1)-1)
      (P3R57.roleCoefficient M hp (P3R57.swapRole e) 0 2-1)=
      (x:ZMod (routingA M.base (P3R57.swapRole e))) := by
    simp only [gridResidue,x,P3R57.swapRole_one,P3R57.roleCoefficient_swap,
      P3R57.routingB_swap,P3R57.routingC_swap,Int.cast_add,Int.cast_mul,Int.cast_natCast]
    simp [Equiv.swap_apply_def,add_comm]
  rw [hgrid'] at hcorner
  have hactual := (actual_unused_merge_swap_iff M e x).mp hcorner
  have hgrid : (x:ZMod a)=gridResidue M.base e (P-1) (C-1) := by
    simp only [x,gridResidue,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  rwa [hgrid] at hactual

theorem mixed_lt_corner (hR3 : (P3R51.internalDegrees M).card=3)
    (hfull : PrincipalFullSupport M e) (D : ℕ)
    (hatt : ∃ n i j, 0<n ∧ n<Q ∧ LTLevel M hp e n i j D)
    (hmax : ∀ n i j d, 0<n → n<Q → LTLevel M hp e n i j d → d≤D) :
    ResidueData.ExactUnusedMergeReverseBase (routingData M.base e)
      (gridResidue M.base e (P-1) (C-1)) := by
  apply shared_protected_lt_corner M hp e hR3 D hatt hmax
  have hprotect := fullsupport_rb_protection M hp (P3R57.swapRole e)
    (fullsupport_swap M e hfull) D
  rw [P3R64.routingH_swapBC M.base e, P3R57.routingA_swap M.base e] at hprotect
  exact hprotect

#print axioms actual_unused_merge_swap_iff
#print axioms rb_swap_iff_lt
#print axioms fullsupport_swap
#print axioms mixed_lt_corner






/-- A nonempty actual RB arm has an attained maximum actual defect. -/
theorem rb_maximum_exists
    (hoccupied : ∃ n i j d, 0<n ∧ n<Q ∧ RBLevel M hp e n i j d) :
    ∃ D, (∃ n i j, 0<n ∧ n<Q ∧ RBLevel M hp e n i j D) ∧
      (∀ n i j d, 0<n → n<Q → RBLevel M hp e n i j d → d≤D) := by
  classical
  let s : Finset ℕ := (Finset.range U).filter (fun d=>∃ n i j,0<n ∧ n<Q ∧ RBLevel M hp e n i j d)
  have hs : s.Nonempty := by
    obtain ⟨n,i,j,d,hn,hnQ,hl⟩ := hoccupied
    exact ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl.2.2.2.2.2.2.2.1,⟨n,i,j,hn,hnQ,hl⟩⟩⟩
  refine ⟨s.max' hs,?_,?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  · intro n i j d hn hnQ hl
    exact Finset.le_max' s d (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl.2.2.2.2.2.2.2.1,⟨n,i,j,hn,hnQ,hl⟩⟩)

/-- A nonempty actual LT arm has an attained maximum actual defect. -/
theorem lt_maximum_exists
    (hoccupied : ∃ n i j d, 0<n ∧ n<Q ∧ LTLevel M hp e n i j d) :
    ∃ D, (∃ n i j, 0<n ∧ n<Q ∧ LTLevel M hp e n i j D) ∧
      (∀ n i j d, 0<n → n<Q → LTLevel M hp e n i j d → d≤D) := by
  classical
  let s : Finset ℕ := (Finset.range W).filter (fun d=>∃ n i j,0<n ∧ n<Q ∧ LTLevel M hp e n i j d)
  have hs : s.Nonempty := by
    obtain ⟨n,i,j,d,hn,hnQ,hl⟩ := hoccupied
    exact ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl.2.2.2.2.2.2.2.1,⟨n,i,j,hn,hnQ,hl⟩⟩⟩
  refine ⟨s.max' hs,?_,?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  · intro n i j d hn hnQ hl
    exact Finset.le_max' s d (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl.2.2.2.2.2.2.2.1,⟨n,i,j,hn,hnQ,hl⟩⟩)

/-- Each occupied RB arm supplies its actual wrapped corner, with no maximum premise. -/
theorem mixed_rb_corner_of_occupied (hR3 : (P3R51.internalDegrees M).card=3)
    (hfull : PrincipalFullSupport M e)
    (hoccupied : ∃ n i j d, 0<n ∧ n<Q ∧ RBLevel M hp e n i j d) :
    ResidueData.ExactUnusedMergeReverseBase (routingData M.base e) (gridResidue M.base e (B-1) (T-1)) := by
  obtain ⟨D,hatt,hmax⟩ := rb_maximum_exists M hp e hoccupied
  exact mixed_rb_corner M hp e hR3 hfull D hatt hmax

/-- Each occupied LT arm supplies its actual wrapped corner, with no maximum premise. -/
theorem mixed_lt_corner_of_occupied (hR3 : (P3R51.internalDegrees M).card=3)
    (hfull : PrincipalFullSupport M e)
    (hoccupied : ∃ n i j d, 0<n ∧ n<Q ∧ LTLevel M hp e n i j d) :
    ResidueData.ExactUnusedMergeReverseBase (routingData M.base e) (gridResidue M.base e (P-1) (C-1)) := by
  obtain ⟨D,hatt,hmax⟩ := lt_maximum_exists M hp e hoccupied
  exact mixed_lt_corner M hp e hR3 hfull D hatt hmax
#print axioms concrete_unused_merge_swap
#print axioms rb_maximum_exists
#print axioms lt_maximum_exists
#print axioms mixed_rb_corner_of_occupied
#print axioms mixed_lt_corner_of_occupied
end
end NS25Lean.P3R67
