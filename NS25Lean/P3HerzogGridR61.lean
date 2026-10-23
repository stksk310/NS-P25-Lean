import NS25Lean.P3RecordIffR60

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R61
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2B4AR1
variable {Gamma : NumericalSemigroup}

theorem canonical_int_grid (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i j : ℤ)
    (hi0 : 0 ≤ i) (hj0 : 0 ≤ j)
    (hi : i < criticalExponent M.base (e 1))
    (hj : j < criticalExponent M.base (e 2))
    (hcorner : i < P3R57.roleCoefficient M hp e 0 1 ∨
      j < P3R57.roleCoefficient M hp e 0 2) :
    P3R60.CanonicalValue M.base e (i*routingB M.base e+j*routingC M.base e) := by
  have hei : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi0
  have hej : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
  have hic : i.toNat < criticalExponent M.base (e 1) := by omega
  have hjc : j.toNat < criticalExponent M.base (e 2) := by omega
  have hcc : i.toNat < P3R57.roleCoefficient M hp e 0 1 ∨
      j.toNat < P3R57.roleCoefficient M hp e 0 2 := by omega
  simpa only [hei,hej] using P3R60.canonical_grid_value M.base e i.toNat j.toNat
    (P3R58.p3_lshape_canonical M hp e _ _ hic hjc hcc)

theorem int_grid_mem (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℤ)
    (hi : 0 ≤ i) (hj : 0 ≤ j) :
    i*routingB B e+j*routingC B e ∈ (routingH B e).asRelativeIdeal := by
  refine ⟨i.toNat*routingB B e+j.toNat*routingC B e, ?_, ?_⟩
  · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨0,i.toNat,j.toNat,by simp⟩
  · simp only [Nat.cast_add,Nat.cast_mul,Int.toNat_of_nonneg hi,Int.toNat_of_nonneg hj]

theorem birthIdeal_subset (H : NumericalSemigroup) (m q : ℕ) (hq : 0 < q)
    (x : ℤ) (hx : x ∈ P3R60.birthIdeal H m q hq) : x ∈ H.asRelativeIdeal := by
  obtain ⟨n,_,_,hn⟩ := hx
  exact hn.1

theorem zero_edges_at_target_residue (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (hq : 0 < q)
    (s : ZMod (routingA B e))
    (hs : L5A2C4I.ResidueData.SourceTargetBranch (P3R60.birthData B e q hq) s)
    (x d : ℤ)
    (hw : (P3R60.birthIdeal (routingH B e) B.q.val q hq).aperyRepresentative
      (routingA B e) ((P3R60.birthData B e q hq).branchTarget s) =
      x+routingB B e+routingC B e+d*routingA B e) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    s = (x : ZMod (routingA B e)) ∧
    (P3R60.birthIdeal (routingH B e) B.q.val q hq).aperyStepQuotient
      (routingA B e) (routingB B e) (routingHB B e) (x : ZMod (routingA B e)) = 0 ∧
    (P3R60.birthIdeal (routingH B e) B.q.val q hq).aperyStepQuotient
      (routingA B e) (routingC B e) (routingHC B e) (x : ZMod (routingA B e)) = 0 := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have he := (P3R60.birthIdeal (routingH B e) B.q.val q hq).aperyRepresentative_mod
    (routingA B e) ((P3R60.birthData B e q hq).branchTarget s)
  rw [hw] at he
  have ht : (P3R60.birthData B e q hq).branchTarget s =
      s+routingB B e+routingC B e := rfl
  rw [ht] at he
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,
    mul_zero,add_zero] at he
  have hse : s = (x : ZMod (routingA B e)) := by linear_combination -he
  refine ⟨hse,?_,?_⟩
  · have hu := hs.1.1
    change (P3R60.birthIdeal (routingH B e) B.q.val q hq).aperyStepQuotient
      (routingA B e) (routingB B e) (routingHB B e) s = 0 at hu
    exact hse ▸ hu
  · have hv := hs.1.2
    change (P3R60.birthIdeal (routingH B e) B.q.val q hq).aperyStepQuotient
      (routingA B e) (routingC B e) (routingHC B e) s = 0 at hv
    exact hse ▸ hv

end NS25Lean.P3R61
