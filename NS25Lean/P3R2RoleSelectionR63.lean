import NS25Lean.P3CommonArmR59

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R63
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4OR5 L5A2B4AR1
open L5A2C4OR3 L5A2C4OR4 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

/-- Swap the first two tail generators before choosing the residue carrier. -/
def swapAB (e : Fin 3 ≃ Fin 3) : Fin 3 ≃ Fin 3 := (Equiv.swap 0 1).trans e

@[simp] theorem swapAB_zero (e : Fin 3 ≃ Fin 3) : swapAB e 0 = e 1 := by simp [swapAB]
@[simp] theorem swapAB_one (e : Fin 3 ≃ Fin 3) : swapAB e 1 = e 0 := by simp [swapAB]
@[simp] theorem swapAB_two (e : Fin 3 ≃ Fin 3) : swapAB e 2 = e 2 := by
  simp [swapAB, Equiv.swap_apply_def]

@[simp] theorem coefficient_swapAB (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i j : Fin 3) :
    P3R57.roleCoefficient M hp (swapAB e) i j =
      P3R57.roleCoefficient M hp e ((Equiv.swap 0 1) i) ((Equiv.swap 0 1) j) := rfl

@[simp] theorem routingD_swapAB (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B (swapAB e) = routingD B e := by
  simp only [routingD, routingN1, routingN2, routingN3, tailValue,
    swapAB_zero, swapAB_one, swapAB_two, tailGcd]
  exact Nat.gcd_left_comm _ _ _

@[simp] theorem routingA_swapAB (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingA B (swapAB e) = routingB B e := by
  simp only [routingA, routingB, routingD_swapAB, routingN1, routingN2, tailValue, swapAB_zero]
@[simp] theorem routingB_swapAB (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingB B (swapAB e) = routingA B e := by
  simp only [routingA, routingB, routingD_swapAB, routingN1, routingN2, tailValue, swapAB_one]
@[simp] theorem routingC_swapAB (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingC B (swapAB e) = routingC B e := by
  simp only [routingC, routingD_swapAB, routingN3, tailValue, swapAB_two]

theorem routingH_swapAB (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingH B (swapAB e) = routingH B e := by
  have extH : ∀ H K : NumericalSemigroup, H.toAddSubmonoid = K.toAddSubmonoid → H = K := by
    intro H K h
    cases H; cases K; cases h; rfl
  apply extH
  ext x
  change x ∈ generatedThree (routingA B (swapAB e)) (routingB B (swapAB e))
    (routingC B (swapAB e)) ↔ x ∈ generatedThree (routingA B e) (routingB B e) (routingC B e)
  simp only [routingA_swapAB, routingB_swapAB, routingC_swapAB,
    generatedThree, Set.insert_comm]

@[simp] theorem principalIndex_swapAB (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    principalIndex (routingH B (swapAB e)) B.q.val B.q_positive =
      principalIndex (routingH B e) B.q.val B.q_positive := by rw [routingH_swapAB]

/-- The actual physical boundary remains third and both other axes remain live. -/
def LegalRole (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) : Prop :=
  killedCount M (criticalExponent M.base (e 2) * weights M.base (e 2)) = 1 ∧
    ∀ i : Fin 3, i ≠ 2 → ∀ k : Fin 3,
      criticalExponent M.base (e i) * weights M.base (e i) - weights M.base k ∈ M.base.apery

theorem legalRole_swapAB (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (h : LegalRole M e) : LegalRole M (swapAB e) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro i hi k
  fin_cases i
  · simpa using h.2 1 (by decide) k
  · simpa using h.2 0 (by decide) k
  · exact False.elim (hi rfl)

/-- Exact six-coefficient transport (P,T,U,V,W,Z) ↦ (U,V,P,T,Z,W). -/
theorem coefficients_swapAB (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) :
    (P3R57.roleCoefficient M hp (swapAB e) 0 1,
      P3R57.roleCoefficient M hp (swapAB e) 0 2,
      P3R57.roleCoefficient M hp (swapAB e) 1 0,
      P3R57.roleCoefficient M hp (swapAB e) 1 2,
      P3R57.roleCoefficient M hp (swapAB e) 2 0,
      P3R57.roleCoefficient M hp (swapAB e) 2 1) =
    (P3R57.roleCoefficient M hp e 1 0, P3R57.roleCoefficient M hp e 1 2,
      P3R57.roleCoefficient M hp e 0 1, P3R57.roleCoefficient M hp e 0 2,
      P3R57.roleCoefficient M hp e 2 1, P3R57.roleCoefficient M hp e 2 0) := by
  simp [coefficient_swapAB, Equiv.swap_apply_def]

/-- An LT return becomes an actual RB return for the newly chosen modulus. -/
theorem ltReturn_swapAB_rb (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (q : ℕ)
    (h : P3R59.LTReturn M hp e q) : P3R59.RBReturn M hp (swapAB e) q := by
  rcases h with ⟨i,t,d,hi,hiP,ht,htV,hd,hdW,he⟩
  have hs := (P3R58.p3_coefficient_sums M hp e).1
  have hrel := (coherent_normalized_relations M.base e (P3R58.p3_coherentHerzogData M hp e)).1
  change criticalExponent M.base (e 0) * routingA M.base e =
    P3R57.roleCoefficient M hp e 0 1 * routingB M.base e +
      P3R57.roleCoefficient M hp e 0 2 * routingC M.base e at hrel
  simp only [P3R59.RBReturn, coefficient_swapAB, routingA_swapAB, routingB_swapAB,
    routingC_swapAB, Equiv.swap_apply_def, Fin.reduceEq, ite_true, ite_false]
  refine ⟨P3R57.roleCoefficient M hp e 2 0-d,t,
    P3R57.roleCoefficient M hp e 0 1-i,by omega,by omega,ht,htV,by omega,by omega,?_⟩
  have hdi : ((P3R57.roleCoefficient M hp e 2 0-d : ℕ) : ℤ) =
      P3R57.roleCoefficient M hp e 2 0 - (d : ℤ) := Int.natCast_sub hdW.le
  have hii : ((P3R57.roleCoefficient M hp e 0 1-i : ℕ) : ℤ) =
      P3R57.roleCoefficient M hp e 0 1 - (i : ℤ) := Int.natCast_sub hiP.le
  have hrelZ : (criticalExponent M.base (e 0) : ℤ) * routingA M.base e =
    (P3R57.roleCoefficient M hp e 0 1 : ℤ) * routingB M.base e +
      (P3R57.roleCoefficient M hp e 0 2 : ℤ) * routingC M.base e := by exact_mod_cast hrel
  have hsZ : (criticalExponent M.base (e 0) : ℤ) =
    (P3R57.roleCoefficient M hp e 1 0 : ℤ) + P3R57.roleCoefficient M hp e 2 0 := by exact_mod_cast hs
  simp only [Nat.cast_add] at he ⊢
  rw [hdi,hii]
  nlinarith only [he,hrelZ,hsZ]

/-- The RB witness is the actual canonical Apéry point, not merely a relation candidate. -/
theorem rbReturn_canonical (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (q : ℕ)
    (h : P3R59.RBReturn M hp e q) :
    ∃ s t d : ℕ, 0 < s ∧ s < P3R57.roleCoefficient M hp e 2 1 ∧
      0 < t ∧ t < P3R57.roleCoefficient M hp e 0 2 ∧
      0 < d ∧ d < P3R57.roleCoefficient M hp e 1 0 ∧
      IsCanonicalTailGridPoint M.base e (P3R57.roleCoefficient M hp e 0 1+s) t ∧
      ((P3R57.roleCoefficient M hp e 0 1+s : ℕ) : ℤ)*routingB M.base e +
        t*routingC M.base e = q*M.base.q.val+d*routingA M.base e := by
  rcases h with ⟨s,t,d,hs,hsZ,ht,htT,hd,hdU,he⟩
  have hc := P3R58.p3_coefficient_sums M hp e
  refine ⟨s,t,d,hs,hsZ,ht,htT,hd,hdU,?_,he⟩
  apply P3R58.p3_lshape_canonical M hp e
  · omega
  · omega
  · exact Or.inr htT

/-- The prescribed LT-to-RB coordinates are (C1-d,j-T,P-i). -/
theorem lt_swapAB_coordinates (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i t d : ℕ)
    (hi : 0 < i) (hiP : i < P3R57.roleCoefficient M hp e 0 1)
    (ht : 0 < t) (htV : t < P3R57.roleCoefficient M hp e 1 2)
    (hd : 0 < d) (hdW : d < P3R57.roleCoefficient M hp e 2 0) :
    P3R57.roleCoefficient M hp (swapAB e) 0 1 +
        (P3R57.roleCoefficient M hp e 2 0-d) = criticalExponent M.base (e 0)-d ∧
      (P3R57.roleCoefficient M hp e 0 2+t)-P3R57.roleCoefficient M hp e 0 2 = t ∧
      IsCanonicalTailGridPoint M.base (swapAB e) (criticalExponent M.base (e 0)-d) t ∧
      0 < P3R57.roleCoefficient M hp e 0 1-i ∧
      P3R57.roleCoefficient M hp e 0 1-i < P3R57.roleCoefficient M hp (swapAB e) 1 0 := by
  have hs := P3R58.p3_coefficient_sums M hp e
  have hc : IsCanonicalTailGridPoint M.base (swapAB e)
      (criticalExponent M.base (e 0)-d) t := by
    apply P3R58.p3_lshape_canonical M hp (swapAB e)
    · simpa using (show criticalExponent M.base (e 0)-d < criticalExponent M.base (e 0) by omega)
    · simpa only [swapAB_two] using (show t < criticalExponent M.base (e 2) by omega)
    · right
      simpa only [coefficient_swapAB, Equiv.swap_apply_def, Fin.reduceEq, ite_true, ite_false] using htV
  simp only [coefficient_swapAB, Equiv.swap_apply_def, Fin.reduceEq, ite_true, ite_false]
  exact ⟨by omega,by omega,hc,by omega,by omega⟩

/-- Independent role selection from the original R2 data; no exceptional counts are transported. -/
theorem r2_legal_rb_role_exists (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR2 : (P3R51.internalDegrees M).card = 2) :
    ∃ e : Fin 3 ≃ Fin 3, LegalRole M e ∧
      ∀ q : ℕ, 0 < q → q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
        P3R59.RBReturn M hp e q := by
  obtain ⟨e,hboundary,hlive⟩ := P3R57.r2_legal_boundary_role M hp hR2
  have hlegal : LegalRole M e := ⟨hboundary,hlive⟩
  rcases P3R59.oneArmPrefix_of_legal_role M hp e hboundary (hlive 0 (by decide)) with hRB | hLT
  · exact ⟨e,hlegal,hRB⟩
  · refine ⟨swapAB e,legalRole_swapAB M e hlegal,?_⟩
    intro q hq hpre
    apply ltReturn_swapAB_rb M hp e q
    exact hLT q hq (by simpa using hpre)

/-- Q=1 is separated from the nonempty RB-prefix branch. -/
theorem r2_legal_rb_or_principal_role_exists (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR2 : (P3R51.internalDegrees M).card = 2) :
    ∃ e : Fin 3 ≃ Fin 3, LegalRole M e ∧
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive = 1 ∨
        (1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive ∧
          ∀ q : ℕ, 0 < q →
            q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
              P3R59.RBReturn M hp e q)) := by
  obtain ⟨e,he,hRB⟩ := r2_legal_rb_role_exists M hp hR2
  refine ⟨e,he,?_⟩
  have hpos := (principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive).1
  by_cases hq : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive = 1
  · exact Or.inl hq
  · exact Or.inr ⟨by omega,hRB⟩

end NS25Lean.P3R63
