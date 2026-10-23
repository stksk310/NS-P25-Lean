import NS25Lean.P3R2RoleSelectionR63
import NS25Lean.P3R2ZeroRectangleR63
import NS25Lean.P3R2FinalCoverR63
import NS25Lean.P3R2PrincipalExclusionR63
import NS25Lean.P3R2ComplementR63
import NS25Lean.P3R2PrincipalShapeR63
import NS25Lean.P3PrincipalRoutingR54

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R63
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1 P3R61
open L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6 CombinatorialCore
variable {Gamma : NumericalSemigroup}
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "P" => P3R57.roleCoefficient M hp e 0 1
local notation "T" => P3R57.roleCoefficient M hp e 0 2
local notation "U" => P3R57.roleCoefficient M hp e 1 0
local notation "V" => P3R57.roleCoefficient M hp e 1 2
local notation "Z" => P3R57.roleCoefficient M hp e 2 1
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

theorem rb_principal_not_final_target (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n≤Q-1 → ∃ i j d, RBLevel M hp e n i j d)
    (hshape : PrincipalPureShape M hp e ∨ PrincipalMixedShape M hp e)
    (s : ZMod a) (hs : ResidueData.SourceTargetBranch (routingData M.base e) s) :
    (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s) ≠
      (Q*M.base.q.val : ℕ) := by
  obtain ⟨i,j,d,hl⟩ := hlevels 1 (by omega) (by omega)
  obtain ⟨i',j',d',hl'⟩ := hlevels (Q-1) (by omega) (by omega)
  have he : (i : ℤ)*b+j*c = (1 : ℤ)*M.base.q.val+d*a := by
    simpa only [Nat.cast_mul,Nat.cast_one] using hl.2.2.2.2.2.2.2.2
  have he' : (i' : ℤ)*b+j'*c = ((Q-1 : ℕ) : ℤ)*M.base.q.val+d'*a := by
    simpa only [Nat.cast_mul] using hl'.2.2.2.2.2.2.2.2
  have hip := hl'.2.2.2.1
  have hjp := hl'.2.1
  rcases hshape with ⟨k,hkT,hkV,hkC,ht⟩ | ⟨L,K,hL,hLW,hK,hKZ,hstrict,ht⟩
  · have hc := rb_complement_pure M hp e 1 (Q-1) i j d i' j' d' k (by omega)
      hl.2.2.2.1 hl'.2.2.2.1 hl.2.1 hl'.2.1 hl.2.2.2.2.2.2.2.1
      hl'.2.2.2.2.2.2.2.1 hkC ht he he'
    have hsum := (P3R58.p3_coefficient_sums M hp e).2.1
    intro hw
    exact rb_pure_principal_not_target M hp e hQ k hkV hkC (by exact_mod_cast ht)
      1 i j d (by omega) (by omega) hl (by omega) (by omega) s hs hw
  · have hc := rb_complement_mixed M hp e 1 (Q-1) i j d i' j' d' L K (by omega)
      hl.2.2.2.1 hl'.2.2.2.1 hl.2.1 hl'.2.1 hl.2.2.2.2.1 hl'.2.2.2.2.1
      hl.2.2.2.2.2.2.2.1 hl'.2.2.2.2.2.2.2.1 hL hLW hKZ ht he he'
    intro hw
    exact rb_mixed_principal_not_target M hp e hQ L K hK hKZ (by exact_mod_cast ht)
      1 i j d (by omega) (by omega) hl (by omega) s hs hw

theorem routing_cExceptional_le_one_of_rb_targets
    (htargets : ∀ s : ResidueData.CSourceTargetBranches (routingData M.base e),
      ∃ n i j d : ℕ, 0<n ∧ n≤Q-1 ∧ RBLevel M hp e n i j d ∧
        (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s.val) =
          (i : ℤ)*b+j*c) :
    ResidueData.cExceptionalCount (routingData M.base e) ≤ 1 := by
  apply cExceptionalCount_le_one_of_rectangle (routingI M.base e) a b c
    (routingHB M.base e) (routingHC M.base e)
    ((normalizedSemigroup_minimal (chosenBase_minimalFour M.base e)).1)
    (quotient_pos_of_dvd (chosenBase_minimalFour M.base e).n₂_pos
      (tailGcd_dvd _ _ _).2.1)
    (quotient_pos_of_dvd (chosenBase_minimalFour M.base e).n₃_pos
      (tailGcd_dvd _ _ _).2.2)
    (routing_ideal_subset M.base e) (criticalExponent M.base (e 1)) T
  · intro x y hx hy
    have hc := canonical_int_grid M hp e (x : ℤ) (y : ℤ) (by positivity) (by positivity)
      (by exact_mod_cast hx) (by have hsum := (P3R58.p3_coefficient_sums M hp e).2.2; exact_mod_cast (by omega : y<criticalExponent M.base (e 2)))
      (Or.inr (by exact_mod_cast hy))
    simpa only [P3R60.CanonicalValue,physicalAlpha,Nat.cast_add,Nat.cast_mul] using hc
  · intro s
    obtain ⟨n,i,j,d,hn,hnq,hl,he⟩ := htargets s
    exact ⟨i,j,hl.1,hl.2.1,hl.2.2.2.2.2.1,hl.2.2.2.2.1,
      by simpa only [P3R60.idealData,routingData,Nat.cast_add,Nat.cast_mul] using he⟩

theorem routing_cExceptional_le_one_of_principal_index_one (hQ : Q=1) :
    ResidueData.cExceptionalCount (routingData M.base e) ≤ 1 := by
  have hc := P3R54.exceptionalCount_le_sourceCount (routingData M.base e)
  have hmin := normalizedSemigroup_minimal (chosenBase_minimalFour M.base e)
  have hb : b ≠ 0 := by intro hz; apply hmin.2.2.1; simpa only [routingB,hz] using (AddSubmonoid.zero_mem _)
  have hc' : c ≠ 0 := by intro hz; apply hmin.2.2.2; simpa only [routingC,hz] using (AddSubmonoid.zero_mem _)
  have hs := (routingI M.base e).concrete_sourceCount_eq_generatorCount a b c hmin.1
    (routingHB M.base e) (routingHC M.base e) hb hc'
  change (routingData M.base e).sourceCount = (routingI M.base e).generatorCount at hs
  rw [hs,P3R62.routingI_eq_principal_translate_of_index_one M.base e hQ,
    RelativeIdeal.generatorCount_translate,P3R54.identity_generatorCount] at hc
  exact hc

theorem legal_rb_final_cExceptional_le_one (hlegal : LegalRole M e)
    (hRB : ∀ n : ℕ, 0<n → n<Q → P3R59.RBReturn M hp e n) :
    ResidueData.cExceptionalCount (routingData M.base e) ≤ 1 := by
  by_cases hQ : Q=1
  · exact routing_cExceptional_le_one_of_principal_index_one M e hQ
  have hpos := (principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive).1
  have hQgt : 1<Q := by omega
  have hlevels : ∀ n, 0<n → n≤Q-1 → ∃ i j d, RBLevel M hp e n i j d := by
    intro n hn hnq
    exact rb_level_exists M hp e n (hRB n hn (by omega))
  have hshape := principal_shapes_of_legal_role M hp e hlegal.1
    (hlegal.2 0 (by decide)) (hlegal.2 1 (by decide))
  have hsimple : (∃ L K : ℕ, 0<L ∧ (Q*M.base.q.val : ℕ)=(L : ℤ)*a+K*b) ∨
      (∃ k : ℕ, T<k ∧ (Q*M.base.q.val : ℕ)=(k : ℤ)*c) := by
    rcases hshape with ⟨k,hkT,hkV,hkC,ht⟩ | ⟨L,K,hL,hLW,hK,hKZ,hstrict,ht⟩
    · exact Or.inr ⟨k,hkT,by exact_mod_cast ht⟩
    · exact Or.inl ⟨L,K,hL,by exact_mod_cast ht⟩
  apply routing_cExceptional_le_one_of_rb_targets M hp e
  intro s
  exact final_rb_target_is_return M hp e hQgt hlevels hsimple
    (rb_principal_not_final_target M hp e hQgt hlevels hshape) s.val s.property
end

theorem r2_selected_final_exceptional_le_one (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (hR2 : (P3R51.internalDegrees M).card=2) :
    ∃ e : Fin 3 ≃ Fin 3, LegalRole M e ∧
      (∀ n : ℕ, 0<n → n<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
        P3R59.RBReturn M hp e n) ∧
      (letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
       ResidueData.cExceptionalCount (routingData M.base e) ≤ 1) := by
  obtain ⟨e,he,hRB⟩ := r2_legal_rb_role_exists M hp hR2
  exact ⟨e,he,hRB,legal_rb_final_cExceptional_le_one M hp e he hRB⟩

theorem r2_original_type_le_rho_sub_two (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (hR2 : (P3R51.internalDegrees M).card=2) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma-2 := by
  obtain ⟨e,_,_,hc⟩ := r2_selected_final_exceptional_le_one M hp hR2
  exact P3R57.type_of_selected_exceptional_le_one M hp e hc
end NS25Lean.P3R63
