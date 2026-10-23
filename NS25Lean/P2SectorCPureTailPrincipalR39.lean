import NS25Lean.P2SectorCPureTailPresentationR39

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR39
open ChosenBase L5A1 L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR3 L5A2C4OR4
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 L5A2C4OR29 FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Reflection center from the actual rectangle; it may be negative. -/
def pureTailF (A : SectorBCriticalRoleBranchA P) : ℤ :=
  (alpha A-1)* (routingB P.M.base A.reindex : ℤ) +
    (d A-1)* (routingC P.M.base A.reindex : ℤ) - routingA P.M.base A.reindex

private theorem rectangle_integer_exists (A : SectorBCriticalRoleBranchA P) (n : ℤ) :
    ∃ k : ℤ, ∃ i j : ℕ, i < alpha A ∧ j < d A ∧
      n = k*routingA P.M.base A.reindex + i*routingB P.M.base A.reindex +
        j*routingC P.M.base A.reindex := by
  obtain ⟨i,j,hi,hj,he⟩ := branchA_residue_rectangle_localization A
    (n : ZMod (routingA P.M.base A.reindex))
  have hmod : (n : ZMod (routingA P.M.base A.reindex)) =
      ((i*routingB P.M.base A.reindex + j*routingC P.M.base A.reindex : ℕ) : ℤ) := by
    simpa only [gridResidue,Int.cast_natCast,Nat.cast_add,Nat.cast_mul,
      Int.cast_add,Int.cast_mul] using he
  obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub n
    ((i*routingB P.M.base A.reindex+j*routingC P.M.base A.reindex : ℕ) : ℤ)
    (routingA P.M.base A.reindex)).mp hmod
  refine ⟨-k,i,j,hi,hj,?_⟩
  simp only [Nat.cast_add,Nat.cast_mul] at hk
  nlinarith only [hk]

private theorem rectangle_integer_mem (A : SectorBCriticalRoleBranchA P)
    {k : ℤ} {i j : ℕ} (hi : i < alpha A) (hj : j < d A) :
    k*routingA P.M.base A.reindex+i*routingB P.M.base A.reindex+
        j*routingC P.M.base A.reindex ∈ (routingH P.M.base A.reindex).asRelativeIdeal ↔
      0 ≤ k := by
  let B := P.M.base
  let e := A.reindex
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  constructor
  · rintro ⟨n,hn,he⟩
    have hc := branchA_rectangle_canonicality A hi hj
    change (normalizedGrid B e 0 i j : ℤ) = physicalAlpha B e (gridResidue B e i j) at hc
    have hmod : ((n : ℤ) : ZMod (routingA B e)) = gridResidue B e i j := by
      change ((n : ℤ) : ZMod (routingA P.M.base A.reindex)) =
        gridResidue P.M.base A.reindex i j
      rw [←he]
      simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,
        mul_zero,zero_add,gridResidue]
    have hle := (routingH B e).asRelativeIdeal.aperyRepresentative_le
      (routingA B e) (gridResidue B e i j) (show (n : ℤ) ∈ (routingH B e).asRelativeIdeal from ⟨n,hn,rfl⟩) hmod
    change physicalAlpha B e (gridResidue B e i j) ≤ (n : ℤ) at hle
    rw [←hc] at hle
    simp only [normalizedGrid,zero_mul,zero_add,Nat.cast_add,Nat.cast_mul] at hle
    nlinarith [he]
  · intro hk
    refine ⟨normalizedGrid B e k.toNat i j,L5A2C4OR33.grid_mem_H B e (k.toNat,i,j),?_⟩
    simp only [normalizedGrid,Nat.cast_add,Nat.cast_mul,Int.toNat_of_nonneg hk]
    rfl

/-- D5: actual normalized-tail symmetry, for all integers including negatives.
This is not a CI statement about the original four-generated Gamma. -/
theorem pure_tail_reflection (A : SectorBCriticalRoleBranchA P) (n : ℤ) :
    n ∉ (routingH P.M.base A.reindex).asRelativeIdeal ↔
      pureTailF A-n ∈ (routingH P.M.base A.reindex).asRelativeIdeal := by
  obtain ⟨k,i,j,hi,hj,he⟩ := rectangle_integer_exists A n
  have ha : 0 < alpha A := by omega
  have hd : 0 < d A := by omega
  have hi' : alpha A-1-i < alpha A := by omega
  have hj' : d A-1-j < d A := by omega
  have hiZ : ((alpha A-1-i : ℕ) : ℤ) = (alpha A : ℤ)-1-i := by omega
  have hjZ : ((d A-1-j : ℕ) : ℤ) = (d A : ℤ)-1-j := by omega
  have hr : pureTailF A-n = (-k-1)*routingA P.M.base A.reindex +
      (alpha A-1-i : ℕ)*routingB P.M.base A.reindex +
      (d A-1-j : ℕ)*routingC P.M.base A.reindex := by
    rw [pureTailF,he,hiZ,hjZ]; ring
  rw [hr, rectangle_integer_mem A hi' hj', he, rectangle_integer_mem A hi hj]
  omega

private theorem principal_cut_iff (H : NumericalSemigroup) {m : ℕ}
    (hm : 0 < m) (hmH : m ∈ H) (n : ℕ) :
    n ∈ cyclicCut H m ↔ (n : ℤ)-m ∈ H.asRelativeIdeal := by
  constructor
  · rintro ⟨_,q,hq,y,hy,he⟩
    refine ⟨(q-1)*m+y,?_,?_⟩
    · exact H.add_mem (H.toAddSubmonoid.nsmul_mem hmH (q-1)) hy
    · have hq' : q-1+1=q := by omega
      rw [he]; push_cast at hq' ⊢; nlinarith
  · rintro ⟨y,hy,he⟩
    have he' : n=m+y := by omega
    refine ⟨he' ▸ H.add_mem hmH hy,1,by omega,y,hy,?_⟩
    simpa using he'

/-- D5: the normalized m-in-H branch returns to the physical Gamma, without
silently replacing Gamma by the normalized four-generator semigroup. -/
theorem pure_tail_principal_type_bound (A : SectorBCriticalRoleBranchA P)
    (hm : routingM P.M.base A.reindex ∈ routingH P.M.base A.reindex) :
    Gamma.asRelativeIdeal.idealType = P.sourceCount ∧ P.sourceCount = 1 := by
  let B := P.M.base
  let e := A.reindex
  let H := routingH B e
  let m := routingM B e
  have hmp : 0 < m := routingM_pos B e
  have hq : firstPrincipal H m hmp = 1 := by
    have hle := firstPrincipal_le H m hmp (by omega : 0 < 1) (by simpa using hm)
    have hpos := (firstPrincipal_spec H m hmp).1
    omega
  have hms : IsMinimalTailGenerator H.toAddSubmonoid (cyclicCut H m) m := by
    simpa [hq] using firstPrincipal_minimal_cut_source H m hmp
  have hsc : Nat.card (ModelSources B e) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨m,hms⟩,?_⟩
    intro t
    obtain ⟨y,hy,he⟩ := (principal_cut_iff H hmp hm t.val).mp t.property.1
    have hte : t.val=m+y := by omega
    have hy0 := ((minimalTail_iff_literal _ _ _).mp t.property).2 m y hms.1 hy hte
    apply Subtype.ext
    change t.val=m
    omega
  have hneg {h : ℕ} (hh : 0 < h) : -(h : ℤ) ∉ H.asRelativeIdeal := by
    rintro ⟨n,_,hn⟩; omega
  have hTH : pureTailF A+m ∈ H.asRelativeIdeal := by
    simpa only [sub_neg_eq_add] using (pure_tail_reflection A (-(m : ℤ))).mp (hneg hmp)
  obtain ⟨T,hT,heT⟩ := hTH
  have hF : pureTailF A ∉ H.asRelativeIdeal := by
    intro hf
    have hz : (0 : ℤ) ∈ H.asRelativeIdeal := ⟨0,H.zero_mem,rfl⟩
    exact ((pure_tail_reflection A 0).mpr (by simpa using hf)) hz
  have hTK : T ∉ cyclicCut H m := by
    intro ht
    have h := (principal_cut_iff H hmp hm T).mp ht
    exact hF (by convert h using 1; omega)
  have htop : ModelTop B e T := by
    refine ⟨hT,hTK,?_⟩
    intro h hh hh0
    apply (principal_cut_iff H hmp hm (T+h)).mpr
    have hf := (pure_tail_reflection A (-(h : ℤ))).mp (hneg (Nat.pos_of_ne_zero hh0))
    convert hf using 1 <;> push_cast <;> omega
  have htc : Nat.card (ModelTops B e) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨T,htop⟩,?_⟩
    intro u
    have hn : (u.val : ℤ)-m ∉ H.asRelativeIdeal := by
      intro hu; exact u.property.2.1 ((principal_cut_iff H hmp hm u.val).mpr hu)
    obtain ⟨h,hh,he⟩ := (pure_tail_reflection A ((u.val : ℤ)-m)).mp hn
    have heq : T=u.val+h := by omega
    have h0 : h=0 := by
      by_contra hh0
      have ht := u.property.2.2 h hh hh0
      rw [←heq] at ht
      exact hTK ht
    apply Subtype.ext
    change u.val=T
    omega
  have hS : P.sourceCount=1 := (pure_model_source_count P e).symm.trans hsc
  have htype : Gamma.asRelativeIdeal.idealType=1 := (pure_model_top_count P e).symm.trans htc
  exact ⟨htype.trans hS.symm,hS⟩

end NS25Lean.L5A2C4OR39
