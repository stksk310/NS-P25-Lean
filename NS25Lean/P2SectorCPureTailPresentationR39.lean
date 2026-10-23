import NS25Lean.P2SectorCPureGeometryR39

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR39

open ChosenBase L5A1 L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR29

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- D0: original physical source count; no role packet or Sector-B input. -/
theorem pure_model_source_count (P : P2Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Nat.card (ModelSources P.M.base e) = P.sourceCount := actual_H_source_count P e

/-- D0/D1: normalized cyclic tops count the type of the *original* Gamma. -/
theorem pure_model_top_count (P : P2Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Nat.card (ModelTops P.M.base e) = Gamma.asRelativeIdeal.idealType :=
  (Nat.card_congr (modelTopsEquivIntegralSocle P.M.base e)).trans
    (L5A2C4OR25.actual_integral_socle_card_eq_type P.M.base e)

/-- D4: equality of normalized tail degrees has a unique rectangle normal
monomial, including its unrestricted nonnegative a-coordinate. -/
theorem pure_tail_normal_unique (A : SectorBCriticalRoleBranchA P) {z w : Monomial}
    (hz : z.2.1 < alpha A ∧ z.2.2 < d A)
    (hw : w.2.1 < alpha A ∧ w.2.2 < d A)
    (he : monomialDegree P.M.base A.reindex z = monomialDegree P.M.base A.reindex w) :
    z = w := by
  have hm (t : Monomial) : monomialDegree P.M.base A.reindex t ≡
      t.2.1 * routingB P.M.base A.reindex + t.2.2 * routingC P.M.base A.reindex
      [MOD routingA P.M.base A.reindex] := by
    simp [Nat.ModEq, monomialDegree, normalizedGrid, Nat.add_mod, Nat.mul_mod]
  have hmod := (hm z).symm.trans (he ▸ hm w)
  obtain ⟨hi, hj⟩ := branchA_rectangle_modEq_unique A hz.1 hz.2 hw.1 hw.2 hmod
  have ha := routingA_pos P.M.base A.reindex
  have hx : z.1 = w.1 := by
    simp only [monomialDegree, normalizedGrid, hi, hj] at he
    nlinarith
  exact Prod.ext hx (Prod.ext hi hj)

/-- The same actual Apéry rectangle, not a global grid canonicality claim. -/
theorem pure_rectangle_height_dictionary (A : SectorBCriticalRoleBranchA P)
    {i j : ℕ} (hi : i < alpha A) (hj : j < d A) :
    IsCanonicalTailGridPoint P.M.base A.reindex i j ∧
      eta P.M.base A.reindex i j = physicalHeight P.M.base A.reindex
        (gridResidue P.M.base A.reindex i j) ∧
      gridLift P.M.base A.reindex i j = 0 := by
  have hc := branchA_rectangle_canonicality A hi hj
  exact ⟨hc, eta_eq_physicalHeight_of_isCanonical P.M.base A.reindex i j hc,
    gridLift_eq_zero_of_isCanonical P.M.base A.reindex i j hc⟩

/-- The two actual critical relations, in the original variable indexing. -/
def pureTailIdeal (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    Ideal (ToricPresentation.Poly k 3) := Ideal.span
      {roleMonomial k A.reindex (0,alpha A,0) - roleMonomial k A.reindex (beta A,0,0),
       roleMonomial k A.reindex (0,0,d A) - roleMonomial k A.reindex (r A,s A,0)}

private def tailQ (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z : Monomial) : ToricPresentation.Poly k 3 ⧸ pureTailIdeal A k :=
  Ideal.Quotient.mk _ (roleMonomial k A.reindex z)

private theorem tailQ_add (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z w : Monomial) : tailQ A k (z+w) = tailQ A k z * tailQ A k w := by
  simp only [tailQ, roleMonomial_add, map_mul]

private theorem tailQ_pure (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    tailQ A k (0,alpha A,0) = tailQ A k (beta A,0,0) := by
  apply Ideal.Quotient.eq.mpr
  exact Ideal.subset_span (Set.mem_insert _ _)

private theorem tailQ_mixed (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    tailQ A k (0,0,d A) = tailQ A k (r A,s A,0) := by
  apply Ideal.Quotient.eq.mpr
  exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem pure_tail_pure_step_degree (A : SectorBCriticalRoleBranchA P)
    (x y z : ℕ) (hy : alpha A ≤ y) :
    monomialDegree P.M.base A.reindex (x,y,z) =
      monomialDegree P.M.base A.reindex (x+beta A,y-alpha A,z) := by
  have h := (branchA_symmetricTailData A).pure_relation
  rw [← routingA_eq_n0 A, ← routingB_eq_n1 A] at h
  simp only [monomialDegree, normalizedGrid, Nat.add_mul]
  have hh := congrArg (fun t => t * routingB P.M.base A.reindex)
    (Nat.sub_add_cancel hy)
  nlinarith only [h, hh]

theorem pure_tail_mixed_step_degree (A : SectorBCriticalRoleBranchA P)
    (x y z : ℕ) (hz : d A ≤ z) :
    monomialDegree P.M.base A.reindex (x,y,z) =
      monomialDegree P.M.base A.reindex (x+r A,y+s A,z-d A) := by
  have h := (branchA_symmetricTailData A).mixed_relation
  rw [← routingA_eq_n0 A, ← routingB_eq_n1 A, ← routingC_eq_n2 A] at h
  simp only [monomialDegree, normalizedGrid, Nat.add_mul]
  have hh := congrArg (fun t => t * routingC P.M.base A.reindex)
    (Nat.sub_add_cancel hz)
  nlinarith only [h, hh]

/-- Terminating two-stage reduction.  The outer measure is z, and the inner
measure is y; mixed reduction may increase y, never the outer measure. -/
theorem pure_tail_quotient_normal_exists (A : SectorBCriticalRoleBranchA P)
    (k : Type*) [Field k] (z : Monomial) :
    ∃ w : Monomial, w.2.1 < alpha A ∧ w.2.2 < d A ∧
      monomialDegree P.M.base A.reindex z = monomialDegree P.M.base A.reindex w ∧
      Ideal.Quotient.mk (pureTailIdeal A k) (roleMonomial k A.reindex z) =
        Ideal.Quotient.mk (pureTailIdeal A k) (roleMonomial k A.reindex w) := by
  have hd : 0 < d A := by
    have hp := (branchA_symmetricTailData A).n0_pos
    rw [(branchA_symmetricTailData A).n0_eq] at hp
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at hp)
  have ha : 0 < alpha A := by
    have hp := (branchA_symmetricTailData A).n0_pos
    rw [(branchA_symmetricTailData A).n0_eq] at hp
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at hp)
  obtain ⟨x,y,z⟩ := z
  change ∃ w : Monomial, w.2.1 < alpha A ∧ w.2.2 < d A ∧
    monomialDegree P.M.base A.reindex (x,y,z) = monomialDegree P.M.base A.reindex w ∧
    tailQ A k (x,y,z) = tailQ A k w
  induction z using Nat.strong_induction_on generalizing x y with
  | h z ih =>
    by_cases hz : d A ≤ z
    · obtain ⟨w,hwy,hwz,hdeg,hq⟩ := ih (z-d A) (by omega) (x+r A) (y+s A)
      refine ⟨w,hwy,hwz,(pure_tail_mixed_step_degree A x y z hz).trans hdeg, ?_⟩
      have h1 : (x,y,z) = (x,y,z-d A)+(0,0,d A) := by ext <;> simp <;> omega
      have h2 : (x+r A,y+s A,z-d A) = (x,y,z-d A)+(r A,s A,0) := by
        ext <;> simp
      have hctx : tailQ A k (x,y,z) = tailQ A k (x+r A,y+s A,z-d A) := by
        rw [h1,h2,tailQ_add,tailQ_add,tailQ_mixed]
      exact hctx.trans hq
    · have hzlt : z < d A := by omega
      induction y using Nat.strong_induction_on generalizing x with
      | h y ihy =>
        by_cases hy : alpha A ≤ y
        · obtain ⟨w,hwy,hwz,hdeg,hq⟩ := ihy (y-alpha A) (by omega) (x+beta A)
          refine ⟨w,hwy,hwz,(pure_tail_pure_step_degree A x y z hy).trans hdeg, ?_⟩
          have h1 : (x,y,z) = (x,y-alpha A,z)+(0,alpha A,0) := by
            ext <;> simp <;> omega
          have h2 : (x+beta A,y-alpha A,z) = (x,y-alpha A,z)+(beta A,0,0) := by
            ext <;> simp
          have hctx : tailQ A k (x,y,z) = tailQ A k (x+beta A,y-alpha A,z) := by
            rw [h1,h2,tailQ_add,tailQ_add,tailQ_pure]
          exact hctx.trans hq
        · exact ⟨(x,y,z),Nat.lt_of_not_ge hy,hzlt,rfl,rfl⟩

/-- Equal actual degrees yield equal quotient monomials, over any field. -/
theorem pure_tail_equal_degree_binomial (A : SectorBCriticalRoleBranchA P)
    (k : Type*) [Field k] {z w : Monomial}
    (he : monomialDegree P.M.base A.reindex z = monomialDegree P.M.base A.reindex w) :
    roleMonomial k A.reindex z - roleMonomial k A.reindex w ∈ pureTailIdeal A k := by
  obtain ⟨z',hzy,hzz,hzd,hzq⟩ := pure_tail_quotient_normal_exists A k z
  obtain ⟨w',hwy,hwz,hwd,hwq⟩ := pure_tail_quotient_normal_exists A k w
  have hn := pure_tail_normal_unique A ⟨hzy,hzz⟩ ⟨hwy,hwz⟩ (hzd.symm.trans (he.trans hwd))
  apply Ideal.Quotient.eq.mp
  exact hzq.trans (by rw [hn]; exact hwq.symm)

/-- D4: exact *polynomial ideal* equality, not just lattice generation. -/
theorem pure_tail_toric_exact (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    P.M.base.IH k = Ideal.span
      {roleMonomial k A.reindex (0,alpha A,0) - roleMonomial k A.reindex (beta A,0,0),
       roleMonomial k A.reindex (0,0,d A) - roleMonomial k A.reindex (r A,s A,0)} := by
  change P.M.base.IH k = pureTailIdeal A k
  apply le_antisymm
  · have hl : (P.M.base.IH k).restrictScalars k ≤ (pureTailIdeal A k).restrictScalars k := by
      rw [L2B2A.IH_eq_span_toricMoves]
      apply Submodule.span_le.mpr
      rintro f ⟨u,v,he,rfl⟩
      let z : Monomial := (u (A.reindex 0),u (A.reindex 1),u (A.reindex 2))
      let w : Monomial := (v (A.reindex 0),v (A.reindex 1),v (A.reindex 2))
      have hu : roleExponent A.reindex z = u := roleExponent_coordinates A.reindex u
      have hv : roleExponent A.reindex w = v := roleExponent_coordinates A.reindex v
      have hd : 0 < routingD P.M.base A.reindex :=
        FourGeneratedBridge.tailGcd_pos (L2B.weights_positive P.M.base (A.reindex 0))
      have heq : monomialDegree P.M.base A.reindex z = monomialDegree P.M.base A.reindex w := by
        apply Nat.eq_of_mul_eq_mul_left hd
        rw [←roleExponent_weight,←roleExponent_weight,hu,hv]
        exact he
      change MvPolynomial.monomial u (1 : k) - MvPolynomial.monomial v 1 ∈ pureTailIdeal A k
      simpa only [roleMonomial,hu,hv] using pure_tail_equal_degree_binomial A k heq
    exact hl
  · apply Ideal.span_le.mpr
    intro f hf
    rcases hf with rfl | hf
    · apply L2B.binomial_mem_IH
      rw [roleExponent_weight,roleExponent_weight]
      congr 1
      simpa [monomialDegree,normalizedGrid,routingA_eq_n0,routingB_eq_n1] using
        (branchA_symmetricTailData A).pure_relation.symm
    · rcases hf with rfl
      apply L2B.binomial_mem_IH
      rw [roleExponent_weight,roleExponent_weight]
      congr 1
      simpa [monomialDegree,normalizedGrid,routingA_eq_n0,routingB_eq_n1,routingC_eq_n2] using
        (branchA_symmetricTailData A).mixed_relation

/-- D2: all positive returns of the first principal, not just one chosen
zero remainder.  No nonfirst-source inference is made from a single return. -/
theorem pure_first_principal_return_unique (H : NumericalSemigroup) (m : ℕ)
    (hm : 0 < m) {n y : ℕ} (hn : 0 < n) (hy : y ∈ H)
    (he : firstPrincipal H m hm * m = n*m+y) :
    n = firstPrincipal H m hm ∧ y = 0 := by
  have hnle : n ≤ firstPrincipal H m hm := by nlinarith
  by_cases heq : n = firstPrincipal H m hm
  · exact ⟨heq,by rw [heq] at he; omega⟩
  have hlt : n < firstPrincipal H m hm := by omega
  have hr : (firstPrincipal H m hm-n)*m = y := by
    rw [Nat.sub_mul]; omega
  have hmin := firstPrincipal_le H m hm (by omega : 0 < firstPrincipal H m hm-n)
    (hr ▸ hy)
  omega

/-- Full-support sources remain at most one without an ActualRolePacket. -/
theorem pure_full_support_source_count_le_one (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Nat.card {s : ModelSources B e // ModelFullSupport B e s.val} ≤ 1 := by
  let : Subsingleton {s : ModelSources B e // ModelFullSupport B e s.val} :=
    ⟨fun s t => Subtype.ext (Subtype.ext
      ((model_full_support_source_is_first B e s.val s.property).trans
        (model_full_support_source_is_first B e t.val t.property).symm))⟩
  simpa using Nat.card_le_card_of_injective
    (fun _ : {s : ModelSources B e // ModelFullSupport B e s.val} => ())
    (fun _ _ _ => Subsingleton.elim _ _)

end NS25Lean.L5A2C4OR39
