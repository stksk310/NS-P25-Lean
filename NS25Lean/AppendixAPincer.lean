import NS25Lean.AppendixAPincerArithmetic
import NS25Lean.AppendixAPincerKillers
import NS25Lean.AppendixAClipClassification

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

theorem weight_layer_coordinates (F : InternalFrontend k M h) (r : ℕ) (u : PlanarExponent) :
    weight M.base (layerExponent F r u) = r * weights M.base (F.normal.perm 0) +
      u 0 * weights M.base (F.normal.perm 1) + u 1 * weights M.base (F.normal.perm 2) := by
  simp only [layerExponent, map_add, weight_single]

theorem apery_pure_below_source (B : Data Gamma) (s : Source B) (i : Fin 3)
    (N ell : ℕ) (hs : s.val = N * weights B i) (ha : ell * weights B i ∈ B.apery) : ell < N := by
  by_contra hn
  apply boundary_not_below_apery B (Finsupp.single i N) (Finsupp.single i ell)
  · simpa only [weight_single, ← hs] using s.property.1
  · simpa only [weight_single] using ha
  · exact Finsupp.single_le_single.mpr (by omega)

/-- The actual Type-II pincer rules out simultaneous effective pure clips
when the full-support source contributes a minimal wrap. -/
theorem typeII_no_simultaneous_clips (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) (hc : 0 < F.normal.c)
    (sfull : Source M.base) (hfull : L3A.FullSupport (G.exponents sfull))
    (hm : wrap F (G.exponents sfull) ∈ L3A.minimalExponents F.initial.ideal)
    (P Q : ℕ) (hP : EffectiveClip F G 0 P) (hQ : EffectiveClip F G 1 Q) : False := by
  classical
  obtain ⟨sY, dY, ell, hsYx, hsYsrc, hdY, hell, haY, hsY, heY⟩ :=
    effective_y_clip_cross_pure F G sfull hfull P hP hc
  obtain ⟨sZ, dZ, mu, hsZx, hsZsrc, hdZ, hmu, haZ, hsZ, heZ⟩ :=
    effective_z_clip_cross_pure F G sfull hfull Q hQ
  obtain ⟨dstar, hdstar, hstar⟩ :=
    full_support_source_residue_zero F sfull ⟨G.exponents sfull, G.degree sfull⟩ hfull
  have hpP := pure_source_clip_bound F G sfull sY hm hsYx 0 P
    (by simpa [planarTie] using hsYsrc)
  have hqQ := pure_source_clip_bound F G sfull sZ hm hsZx 1 Q
    (by simpa [planarTie] using hsZsrc)
  have hdepthY := cross_pure_depth_lt F G sfull hfull dstar hstar sY
    (F.normal.perm 2) dY ell hell haY heY
  have hdepthZ := cross_pure_depth_lt F G sfull hfull dstar hstar sZ
    (F.normal.perm 1) dZ mu hmu haZ heZ
  have hEll := apery_pure_below_source M.base sZ (F.normal.perm 2) (F.normal.c + Q) ell hsZ haY
  have hMu := apery_pure_below_source M.base sY (F.normal.perm 1) (F.normal.b + P) mu hsY haZ
  let u : PlanarExponent := Finsupp.single 0 (F.normal.b + P - mu) +
    Finsupp.single 1 (F.normal.c + Q - ell)
  have hu0 : u 0 = F.normal.b + P - mu := by simp [u]
  have hu1 : u 1 = F.normal.c + Q - ell := by simp [u]
  have hsubY : (F.normal.b + P - mu) * weights M.base (F.normal.perm 1) +
      mu * weights M.base (F.normal.perm 1) =
      (F.normal.b + P) * weights M.base (F.normal.perm 1) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hMu.le]
  have hsubZ : (F.normal.c + Q - ell) * weights M.base (F.normal.perm 2) +
      ell * weights M.base (F.normal.perm 2) =
      (F.normal.c + Q) * weights M.base (F.normal.perm 2) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hEll.le]
  have huWeight : weight M.base (layerExponent F 0 u) = (dY + dZ) * M.base.q.val := by
    rw [weight_layer_coordinates, zero_mul, zero_add, hu0, hu1, Nat.add_mul]
    omega
  have huK := degree_in_K_of_positive_pivot M.base (layerExponent F 0 u) 0 (dY + dZ)
    Gamma.toAddSubmonoid.zero_mem (by omega) (by simpa using huWeight)
  have hkill := pincer_killer_classification F G hq sfull hfull P Q
    (effectiveClip_positive F G hP) (effectiveClip_positive F G hQ) hP.1 hQ.1 hP.2 hQ.2 u
    (boundary_mem_initial F _ huK) (by omega) (by omega)
  have hkill0 := hkill 0
  have hkill1 := hkill 1
  simp [planarTie, hu0, hu1] at hkill0 hkill1
  have hstarDegree : G.exponents sfull (F.normal.perm 0) * weights M.base (F.normal.perm 0) +
      planarSource F G sfull 0 * weights M.base (F.normal.perm 1) +
      planarSource F G sfull 1 * weights M.base (F.normal.perm 2) = dstar * M.base.q.val := by
    have hh := congrArg (weight M.base) (layerExponent_projection F (G.exponents sfull))
    rw [weight_layer_coordinates, G.degree, hstar] at hh
    exact hh
  exact pincer_depth_contradiction F sY sZ (G.exponents sfull (F.normal.perm 0))
    (planarSource F G sfull 0) (planarSource F G sfull 1) P Q ell mu dY dZ dstar
    (hfull _) (G.slab sfull) hpP hqQ hdepthY hdepthZ hsY hsZ (hsY.symm.trans heY)
    (hsZ.symm.trans heZ) hstarDegree (by omega) (by omega)

end NS25Lean.L3C
