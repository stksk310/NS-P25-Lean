import NS25Lean.P3ActualInsertionR62
import NS25Lean.P3R2FinalAxisR63

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R63
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open L5A2C4OR3 P3R61
variable {Gamma : NumericalSemigroup}

theorem canonical_zero_edge_contradiction {H : NumericalSemigroup}
    (I : RelativeIdeal H) (a h : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (hh : h ∈ H)
    (x y : ℤ) (K k : ℕ)
    (hcan : H.asRelativeIdeal.aperyRepresentative a (x : ZMod a)=x)
    (hmem : x ∈ I) (hopp : x+h=y+(a : ℤ)*K)
    (hz : I.aperyStepQuotient a h hh (x : ZMod a)=0)
    (hcand : y+(a : ℤ)*k ∈ I) (hlt : k<K) : False := by
  have hrep : I.aperyRepresentative a (x : ZMod a)=x := by
    apply le_antisymm (I.aperyRepresentative_le a _ hmem rfl)
    have hl := H.asRelativeIdeal.aperyRepresentative_le a _
      (hsub _ (I.aperyRepresentative_mem a (x : ZMod a))) (I.aperyRepresentative_mod a _)
    rwa [hcan] at hl
  have he := I.apery_step_eq a h hh (x : ZMod a)
  rw [hz,hrep] at he
  simp only [Nat.cast_zero,mul_zero,add_zero] at he
  have hm : ((y+(a : ℤ)*k : ℤ) : ZMod a) = (x : ZMod a)+h := by
    have ht := congrArg (fun z : ℤ => (z : ZMod a)) hopp
    simpa using ht.symm
  have hl := I.aperyRepresentative_le a ((x : ZMod a)+h) hcand hm
  have ha : (0 : ℤ)<a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have hk : (k : ℤ)<K := by exact_mod_cast hlt
  nlinarith

theorem routing_ideal_subset (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x : ℤ) (hx : x ∈ routingI B e) : x ∈ (routingH B e).asRelativeIdeal := by
  obtain ⟨n,hn,hmem,_⟩ := (mem_routingI_iff_positive_return B e x).mp hx
  exact hmem

theorem completed_prefix_subset_final (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH B e) B.q.val B.q_positive)
    (x : ℤ) (hx : x ∈ P3R60.birthIdeal (routingH B e) B.q.val
      (principalIndex (routingH B e) B.q.val B.q_positive-1) (by omega)) :
    x ∈ routingI B e := by
  rw [P3R62.routingI_eq_inserted_ideal B e hQ]
  exact Or.inl hx

section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "T" => P3R57.roleCoefficient M hp e 0 2
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local notation "C2" => criticalExponent M.base (e 1)
local notation "C3" => criticalExponent M.base (e 2)
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

theorem rb_final_canonical_divisor (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n≤Q-1 → ∃ i j d, RBLevel M hp e n i j d)
    (hshape : (∃ L I : ℕ, 0<L ∧ (Q*M.base.q.val : ℕ) = (L : ℤ)*a+I*b) ∨
      (∃ k : ℕ, T<k ∧ (Q*M.base.q.val : ℕ) = (k : ℤ)*c))
    (i j : ℕ) (hi : i<C2) (hj : j<T)
    (hm : (i : ℤ)*b+j*c ∈ routingI M.base e) :
    ∃ n x y d, 0<n ∧ n≤Q-1 ∧ RBLevel M hp e n x y d ∧ x ≤ i ∧ y ≤ j := by
  have hs := P3R58.p3_coefficient_sums M hp e
  have hjC : j<C3 := by omega
  have hcan := P3R60.canonical_grid_value M.base e i j
    (P3R58.p3_lshape_canonical M hp e i j hi hjC (Or.inr hj))
  rw [P3R62.routingI_eq_inserted_ideal M.base e hQ] at hm
  rcases hm with hm | hm
  · exact rb_canonical_prefix_divisor M hp e (Q-1) (by omega) hlevels i j hi hjC (Or.inr hj) hm
  · change (i : ℤ)*b+j*c-(Q*M.base.q.val : ℕ) ∈ (routingH M.base e).asRelativeIdeal at hm
    rcases hshape with ⟨L,I,hL,he⟩ | ⟨k,hk,he⟩
    · have htail := routing_combination_mem M.base e 0 I 0 le_rfl (Nat.cast_nonneg _) le_rfl
      have hadd := ideal_add_int (routingH M.base e).asRelativeIdeal htail hm
      exfalso
      apply canonical_not_positive_a M hp e i j hi hjC (Or.inr hj) L (by exact_mod_cast hL)
        ((I : ℤ)*b+((i : ℤ)*b+j*c-(Q*M.base.q.val : ℕ)))
        (by simpa only [zero_mul,zero_add,add_zero] using hadd)
      rw [he]; ring
    · rw [he] at hm
      have hc := canonical_residual_coordinates M.base e i j 0 k hi hjC hcan
        (by simpa using hm)
      omega

theorem routing_zero_edges_at_target (s : ZMod a)
    (hs : ResidueData.SourceTargetBranch (routingData M.base e) s)
    (x d : ℤ)
    (hw : (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s) =
      x+b+c+d*a) :
    s = (x : ZMod a) ∧
    (routingI M.base e).aperyStepQuotient a b (routingHB M.base e) (x : ZMod a)=0 ∧
    (routingI M.base e).aperyStepQuotient a c (routingHC M.base e) (x : ZMod a)=0 := by
  have he := (routingI M.base e).aperyRepresentative_mod a ((routingData M.base e).branchTarget s)
  rw [hw] at he
  have ht : (routingData M.base e).branchTarget s = s+b+c := rfl
  rw [ht] at he
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,mul_zero,add_zero] at he
  have hse : s=(x : ZMod a) := by linear_combination -he
  refine ⟨hse,?_,?_⟩
  · have hu := hs.1.1
    change (routingI M.base e).aperyStepQuotient a b (routingHB M.base e) s=0 at hu
    exact hse ▸ hu
  · have hv := hs.1.2
    change (routingI M.base e).aperyStepQuotient a c (routingHC M.base e) s=0 at hv
    exact hse ▸ hv
end
end NS25Lean.P3R63
