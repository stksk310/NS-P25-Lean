import NS25Lean.AppendixAEndpoints

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

theorem source_boundary_no_positive_translate (B : Data Gamma) (s : Source B)
    (u v : ℕ) (hu : u ∈ B.K) (hv : v ∈ B.H) (hp : 0 < v) (he : s.val = u + v) : False := by
  rcases s.property.2 v hv hp.ne' with hn | hn
  · omega
  · apply hn
    convert hu using 1 <;> omega

theorem source_pure_boundary_lower_bound (B : Data Gamma) (s : Source B) (i : Fin 3)
    (N d : ℕ) (hs : s.val = N * weights B i) (hd : d * weights B i ∈ B.K) : N ≤ d := by
  by_contra hn
  have hlt : d < N := by omega
  apply source_boundary_no_positive_translate B s (d * weights B i) ((N - d) * weights B i) hd
  · exact B.H.nsmul_mem (B.tailDegrees i).property _
  · exact Nat.mul_pos (Nat.sub_pos_of_lt hlt) (weights_positive B i)
  · rw [← Nat.add_mul, Nat.add_sub_of_le hlt.le]
    exact hs

theorem degree_in_K_of_positive_pivot (B : Data Gamma) (u : Fin 3 →₀ ℕ)
    (ω d : ℕ) (hω : ω ∈ Gamma.toAddSubmonoid) (hd : 1 ≤ d)
    (he : weight B u = ω + d * B.q.val) : weight B u ∈ B.K := by
  have hdm : d * B.q.val = (d - 1) * B.q.val + B.q.val := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel hd]
  refine ⟨weight_mem_H B u, ?_, ?_⟩
  · omega
  · have hm : ω + (d - 1) * B.q.val ∈ Gamma.toAddSubmonoid :=
      Gamma.toAddSubmonoid.add_mem hω (by
        simpa only [nsmul_eq_mul, Nat.cast_id, L2B.weights] using Gamma.toAddSubmonoid.nsmul_mem B.q.property (d - 1))
    convert hm using 1 <;> omega

theorem apery_weight_of_le (B : Data Gamma) (u v : Fin 3 →₀ ℕ)
    (hle : u ≤ v) (hv : weight B v ∈ B.apery) : weight B u ∈ B.apery := by
  rw [B.apery_eq_compl]
  exact ⟨weight_mem_H B u, fun hu => boundary_not_below_apery B u v hu hv hle⟩

/-- Arithmetic end of the source-faithful pincer. The upper bounds are the
separate actual-killer-classification output, not a compensation assumption. -/
theorem pincer_depth_contradiction (F : InternalFrontend k M h)
    (sY sZ : Source M.base) (r p q P Q ell mu dY dZ dstar : ℕ)
    (hr : 0 < r) (hra : r < F.normal.a) (hpP : p < P) (hqQ : q < Q)
    (hdY : dY < dstar) (hdZ : dZ < dstar)
    (hY : sY.val = (F.normal.b + P) * weights M.base (F.normal.perm 1))
    (hZ : sZ.val = (F.normal.c + Q) * weights M.base (F.normal.perm 2))
    (hYeq : (F.normal.b + P) * weights M.base (F.normal.perm 1) =
      ell * weights M.base (F.normal.perm 2) + dY * M.base.q.val)
    (hZeq : (F.normal.c + Q) * weights M.base (F.normal.perm 2) =
      mu * weights M.base (F.normal.perm 1) + dZ * M.base.q.val)
    (hstar : r * weights M.base (F.normal.perm 0) + p * weights M.base (F.normal.perm 1) +
      q * weights M.base (F.normal.perm 2) = dstar * M.base.q.val)
    (hmu : mu ≤ P - p) (hell : ell ≤ Q - q) : False := by
  let X := weights M.base (F.normal.perm 0)
  let Y := weights M.base (F.normal.perm 1)
  let Z := weights M.base (F.normal.perm 2)
  have htie := F.normal.degree_equality.1.trans F.normal.degree_equality.2.symm
  have har : (F.normal.a - r) * X + r * X = F.normal.a * X := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hra.le]
  have hP : (P - p) * Y + p * Y = P * Y := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hpP.le]
  have hQ : (Q - q) * Z + q * Z = Q * Z := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hqQ.le]
  have hDY : (dstar - dY) * M.base.q.val + dY * M.base.q.val = dstar * M.base.q.val := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hdY.le]
  have hDZ : (dstar - dZ) * M.base.q.val + dZ * M.base.q.val = dstar * M.base.q.val := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hdZ.le]
  have hrevY : (F.normal.b + p + mu) * Y = (F.normal.a - r) * X +
      (Q - q) * Z + (dstar - dZ) * M.base.q.val := by
    dsimp [X, Y, Z] at *
    simp only [Nat.add_mul] at *
    omega
  have hrevZ : (F.normal.c + q + ell) * Z = (F.normal.a - r) * X +
      (P - p) * Y + (dstar - dY) * M.base.q.val := by
    dsimp [X, Y, Z] at *
    simp only [Nat.add_mul] at *
    omega
  have hΓ (i : Fin 3) (n : ℕ) : n * weights M.base i ∈ Gamma.toAddSubmonoid := by
    simpa only [nsmul_eq_mul, Nat.cast_id, L2B.weights] using Gamma.toAddSubmonoid.nsmul_mem
      (M.base.H_le (M.base.tailDegrees i).property) n
  have hkY : (F.normal.b + p + mu) * Y ∈ M.base.K := by
    have hh := degree_in_K_of_positive_pivot M.base
      (Finsupp.single (F.normal.perm 1) (F.normal.b + p + mu))
      ((F.normal.a - r) * X + (Q - q) * Z) (dstar - dZ)
      (Gamma.toAddSubmonoid.add_mem (hΓ _ _) (hΓ _ _)) (by omega)
      (by simpa only [weight_single, Y] using hrevY)
    simpa only [weight_single, Y] using hh
  have hkZ : (F.normal.c + q + ell) * Z ∈ M.base.K := by
    have hh := degree_in_K_of_positive_pivot M.base
      (Finsupp.single (F.normal.perm 2) (F.normal.c + q + ell))
      ((F.normal.a - r) * X + (P - p) * Y) (dstar - dY)
      (Gamma.toAddSubmonoid.add_mem (hΓ _ _) (hΓ _ _)) (by omega)
      (by simpa only [weight_single, Z] using hrevZ)
    simpa only [weight_single, Z] using hh
  have hmuLower := source_pure_boundary_lower_bound M.base sY (F.normal.perm 1)
    (F.normal.b + P) (F.normal.b + p + mu) hY hkY
  have hellLower := source_pure_boundary_lower_bound M.base sZ (F.normal.perm 2)
    (F.normal.c + Q) (F.normal.c + q + ell) hZ hkZ
  have hmueq : mu = P - p := by omega
  have helleq : ell = Q - q := by omega
  have hres : (F.normal.a - r) * X + dstar * M.base.q.val = (dY + dZ) * M.base.q.val := by
    rw [hmueq] at hZeq
    rw [helleq] at hYeq
    dsimp [X, Y, Z] at *
    simp only [Nat.add_mul] at *
    omega
  have hpos : 0 < (F.normal.a - r) * X := Nat.mul_pos (Nat.sub_pos_of_lt hra) (weights_positive _ _)
  have hds : dstar ≤ dY + dZ := by
    by_contra hn
    have hm := Nat.mul_le_mul_right M.base.q.val (show dY + dZ ≤ dstar from by omega)
    omega
  have hdm : (dY + dZ - dstar) * M.base.q.val + dstar * M.base.q.val =
      (dY + dZ) * M.base.q.val := by rw [← Nat.add_mul, Nat.sub_add_cancel hds]
  have ha : (F.normal.a - r) * X ∈ M.base.apery := by
    have hh := apery_weight_of_le M.base (Finsupp.single (F.normal.perm 0) (F.normal.a - r))
      F.normal.alpha.val (by rw [F.normal.alpha_eq]; exact Finsupp.single_le_single.mpr (Nat.sub_le _ _))
      (by rw [F.normal.alpha.property]; exact F.normal.apery)
    simpa only [weight_single, X] using hh
  have hz : 0 ∈ M.base.apery := by
    constructor
    · exact Gamma.toAddSubmonoid.zero_mem
    · exact Or.inl M.base.q_positive
  have heq := apery_shift_eq M.base (d := dY + dZ - dstar) hz ha (by omega)
  omega

end NS25Lean.L3C
