import NS25Lean.P3LTAxisExclusionR61
import NS25Lean.P3RBAxisExclusionR61
import NS25Lean.P3PrefixSourceReductionR60

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R61
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4I L5A2B4AR1
variable {Gamma : NumericalSemigroup}

theorem minimal_generator_eq_of_residual {H : NumericalSemigroup} (I : RelativeIdeal H)
    (w g : ℤ) (hw : I.IsMinimalGenerator w) (hg : g ∈ I)
    (hres : w-g ∈ H.asRelativeIdeal) : w = g := by
  obtain ⟨k,hk,he⟩ := hres
  have hk0 : k = 0 := by
    by_contra hn
    apply hw.2 k hk hn
    convert hg using 1 <;> omega
  rw [hk0] at he
  omega

theorem completed_prefix_mixed_support (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (harm : P3R59.OneArmPrefix M hp e) (q : ℕ) (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (s : ZMod (routingA M.base e))
    (hs : ResidueData.SourceTargetBranch (P3R60.birthData M.base e q hq) s) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    ∃ i j : ℕ, 0 < i ∧ 0 < j ∧
      (P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq).aperyRepresentative
        (routingA M.base e) ((P3R60.birthData M.base e q hq).branchTarget s) =
        (i : ℤ)*routingB M.base e+j*routingC M.base e := by
  let a := routingA M.base e
  let b := routingB M.base e
  let c := routingC M.base e
  let I := P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq
  let D := P3R60.birthData M.base e q hq
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  let w := I.aperyRepresentative a (D.branchTarget s)
  have hgen : (routingH M.base e).IsGeneratedByThree a b c := rfl
  have hbpos : 0 < b := quotient_pos_of_dvd (chosenBase_minimalFour M.base e).n₂_pos
    (tailGcd_dvd _ _ _).2.1
  have hcpos : 0 < c := quotient_pos_of_dvd (chosenBase_minimalFour M.base e).n₃_pos
    (tailGcd_dvd _ _ _).2.2
  have hsource := hs.2
  have hmin : I.IsMinimalGenerator w :=
    (I.concrete_isSource_iff_isMinimalGenerator a b c hgen (routingHB M.base e)
      (routingHC M.base e) (Nat.ne_of_gt hbpos) (Nat.ne_of_gt hcpos) (D.branchTarget s)).mp hsource
  rcases harm with harm | harm
  · have hlevels : ∀ n : ℕ, 0 < n → n ≤ q → ∃ i j d : ℕ, RBLevel M hp e n i j d := by
      intro n hn hnq
      exact rb_level_exists M hp e n (harm n hn (by omega))
    obtain ⟨n,i,j,d,hn,hnq,hl,hres⟩ := rb_prefix_cover M hp e q hq hlevels w hmin.1
    rcases hres with hres | hres | hres
    · have heq := minimal_generator_eq_of_residual I w _ hmin
        (rb_level_beta_mem M hp e q hq n i j d hn hnq hl) hres
      exact ⟨i,j,hl.1,hl.2.1,heq⟩
    · have heq := minimal_generator_eq_of_residual I w _ hmin
        (rb_level_axes_mem M hp e q hq n i j d hn hnq hl).1 hres
      exact (rb_axisA_not_target M hp e q hq hlevels n i j d hn hnq hl s hs heq).elim
    · have heq := minimal_generator_eq_of_residual I w _ hmin
        (rb_level_axes_mem M hp e q hq n i j d hn hnq hl).2 hres
      exact (rb_axisB_not_target M hp e q hq hlevels n i j d hn hnq hl s hs heq).elim
  · have hlevels : ∀ n : ℕ, 0 < n → n ≤ q → ∃ i j d : ℕ, LTLevel M hp e n i j d := by
      intro n hn hnq
      exact lt_level_exists M hp e n (harm n hn (by omega))
    obtain ⟨n,i,j,d,hn,hnq,hl,hres⟩ := lt_prefix_cover M hp e q hq hlevels w hmin.1
    rcases hres with hres | hres | hres
    · have heq := minimal_generator_eq_of_residual I w _ hmin
        (lt_level_beta_mem M hp e q hq n i j d hn hnq hl) hres
      exact ⟨i,j,hl.1,hl.2.1,heq⟩
    · have heq := minimal_generator_eq_of_residual I w _ hmin
        (lt_level_axes_mem M hp e q hq n i j d hn hnq hl).1 hres
      exact (lt_axisA_not_target M hp e q hq hlevels n i j d hn hnq hl s hs heq).elim
    · have heq := minimal_generator_eq_of_residual I w _ hmin
        (lt_level_axes_mem M hp e q hq n i j d hn hnq hl).2 hres
      exact (lt_axisB_not_target M hp e q hq hlevels n i j d hn hnq hl s hs heq).elim

theorem g3SupportGoal (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR2 : (P3R51.internalDegrees M).card = 2) :
  ∃ e : Fin 3 ≃ Fin 3,
    killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1 ∧
    (∀ i : Fin 3, i≠2 → ∀ k : Fin 3,
      criticalExponent M.base (e i)*weights M.base (e i)-weights M.base k ∈ M.base.apery) ∧
    P3R59.OneArmPrefix M hp e ∧
    ∀ hQ : 1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive,
      let q := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive-1
      let hq : 0 < q := by omega
      letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      let I := P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq
      let D := P3R60.birthData M.base e q hq
      ∀ s : ZMod (routingA M.base e), ResidueData.SourceTargetBranch D s →
        ∃ i j : ℕ, 0 < i ∧ 0 < j ∧
          I.aperyRepresentative (routingA M.base e) (D.branchTarget s) =
            (i : ℤ)*routingB M.base e+j*routingC M.base e := by
  obtain ⟨e,hkill,hlive,harm,_⟩ := P3R60.r2_record_iff_exists M hp hR2
  refine ⟨e,hkill,hlive,harm,?_⟩
  intro hQ
  dsimp only
  intro s hs
  exact completed_prefix_mixed_support M hp e harm _ (by omega) (by omega) s hs

end NS25Lean.P3R61
