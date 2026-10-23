import NS25Lean.AppendixBQuotient

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A

theorem two_generator_ordered_difference (A B x y x' y' : ℕ)
    (hb : 0 < B) (hc : A.Coprime B) (he : A * x + B * y = A * x' + B * y')
    (hle : x ≤ x') : ∃ t : ℕ, x' = x + B * t ∧ y = y' + A * t := by
  obtain ⟨t, hx, hy⟩ := two_generator_difference A B x y x' y' hb hc he
  have ht : 0 ≤ t := by
    have hleI : (x : ℤ) ≤ x' := by exact_mod_cast hle
    have hbI : (0 : ℤ) < B := by exact_mod_cast hb
    nlinarith
  lift t to ℕ using ht
  refine ⟨t, ?_, ?_⟩
  · exact_mod_cast (show (x' : ℤ) = x + B * t by linarith)
  · exact_mod_cast (show (y : ℤ) = y' + A * t by linarith)

/-- A primitive pair relation identifies every two-variable monomial of equal weight.
No cancellation in the additive congruence is assumed. -/
theorem pair_congruence {M : Type*} [AddCommMonoid M] (c : AddCon M) (X Y : M)
    (A B : ℕ) (hb : 0 < B) (hc : A.Coprime B) (hrel : c (B • X) (A • Y))
    (x y x' y' : ℕ) (he : A * x + B * y = A * x' + B * y') :
    c (x • X + y • Y) (x' • X + y' • Y) := by
  have step (x y x' y' : ℕ) (he : A * x + B * y = A * x' + B * y') (hle : x ≤ x') :
      c (x • X + y • Y) (x' • X + y' • Y) := by
    obtain ⟨t, hx, hy⟩ := two_generator_ordered_difference A B x y x' y' hb hc he hle
    rw [hx, hy]
    have ht := c.add (c.refl (x • X + y' • Y)) (c.symm (c.nsmul t hrel))
    convert ht using 1 <;> simp only [add_nsmul, mul_nsmul] <;> ac_rfl
  rcases le_total x x' with h | h
  · exact step x y x' y' he h
  · exact c.symm (step x' y' x y he.symm h)

/-- The two primitive pair relations and the cross relation identify every
four-variable factorization of the same glued degree. -/
theorem gluing_congruence {M : Type*} [AddCommMonoid M] (q : AddCon M) (X Y Z W : M)
    (u v a b c d r s k l : ℕ) (hv : 0 < v) (hb : 0 < b) (hd : 0 < d)
    (hab : a.Coprime b) (hcd : c.Coprime d) (huv : u.Coprime v)
    (hvr : v = a * r + b * s) (huk : u = c * k + d * l)
    (hfirst : q (b • X) (a • Y)) (hsecond : q (d • Z) (c • W))
    (hcross : q (r • X + s • Y) (k • Z + l • W))
    (x y z w x' y' z' w' : ℕ)
    (he : u * (a * x + b * y) + v * (c * z + d * w) =
      u * (a * x' + b * y') + v * (c * z' + d * w')) :
    q ((x • X + y • Y) + (z • Z + w • W))
      ((x' • X + y' • Y) + (z' • Z + w' • W)) := by
  have step (x y z w x' y' z' w' : ℕ)
      (he : u * (a * x + b * y) + v * (c * z + d * w) =
        u * (a * x' + b * y') + v * (c * z' + d * w'))
      (hle : a * x + b * y ≤ a * x' + b * y') :
      q ((x • X + y • Y) + (z • Z + w • W))
        ((x' • X + y' • Y) + (z' • Z + w' • W)) := by
    obtain ⟨t, hA, hB⟩ := two_generator_ordered_difference u v
      (a * x + b * y) (c * z + d * w) (a * x' + b * y') (c * z' + d * w') hv huv he hle
    have hp := pair_congruence q X Y a b hb hab hfirst
      (x + t * r) (y + t * s) x' y' (by
        calc
          a * (x + t * r) + b * (y + t * s) = a * x + b * y + (a * r + b * s) * t := by ring
          _ = a * x' + b * y' := by rw [← hvr, ← hA])
    have hq := pair_congruence q Z W c d hd hcd hsecond
      z w (z' + t * k) (w' + t * l) (by
        calc
          c * z + d * w = c * z' + d * w' + (c * k + d * l) * t := by rw [← huk, ← hB]
          _ = c * (z' + t * k) + d * (w' + t * l) := by ring)
    have hp' : q ((x • X + y • Y) + t • (r • X + s • Y)) (x' • X + y' • Y) := by
      convert hp using 1 <;> simp only [add_nsmul, nsmul_add, ← mul_nsmul, mul_comm] <;> ac_rfl
    have hq' : q (z • Z + w • W) ((z' • Z + w' • W) + t • (k • Z + l • W)) := by
      convert hq using 1 <;> simp only [add_nsmul, nsmul_add, ← mul_nsmul, mul_comm] <;> ac_rfl
    have hm := q.add (q.refl ((x • X + y • Y) + (z' • Z + w' • W)))
      (q.symm (q.nsmul t hcross))
    have hm' : q ((x • X + y • Y) + ((z' • Z + w' • W) + t • (k • Z + l • W)))
        (((x • X + y • Y) + t • (r • X + s • Y)) + (z' • Z + w' • W)) := by
      convert hm using 1 <;> ac_rfl
    exact q.trans (q.add (q.refl _) hq') (q.trans hm' (q.add hp' (q.refl _)))
  rcases le_total (a * x + b * y) (a * x' + b * y') with h | h
  · exact step x y z w x' y' z' w' he h
  · exact q.symm (step x' y' z' w' x y z w he.symm h)

end NS25Lean.L4A
