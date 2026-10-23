import NS25Lean.AppendixBQuotient

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A
open ChosenBase L2C
variable {Gamma : NumericalSemigroup} {B : Data Gamma}
namespace NormalizedPairs

def leftMonomial (N : NormalizedPairs B) (x y : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (N.perm 0) x + Finsupp.single (N.perm 1) y

def rightMonomial (N : NormalizedPairs B) (x y : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (N.perm 2) x + Finsupp.single (N.perm 3) y

def leftPart (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) : Fin 4 →₀ ℕ :=
  N.leftMonomial (f (N.perm 0)) (f (N.perm 1))

def rightPart (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) : Fin 4 →₀ ℕ :=
  N.rightMonomial (f (N.perm 2)) (f (N.perm 3))

def leftValue (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) : ℕ :=
  N.alpha * f (N.perm 0) + N.beta * f (N.perm 1)

def rightValue (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) : ℕ :=
  N.gamma * f (N.perm 2) + N.delta * f (N.perm 3)

def LeftSupported (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) : Prop :=
  f (N.perm 2) = 0 ∧ f (N.perm 3) = 0

def RightSupported (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) : Prop :=
  f (N.perm 0) = 0 ∧ f (N.perm 1) = 0

@[simp] theorem leftMonomial_apply (N : NormalizedPairs B) (x y : ℕ) (k : Fin 4) :
    N.leftMonomial x y (N.perm k) = if k = 0 then x else if k = 1 then y else 0 := by
  fin_cases k <;> simp [leftMonomial, N.perm.injective.eq_iff]

@[simp] theorem rightMonomial_apply (N : NormalizedPairs B) (x y : ℕ) (k : Fin 4) :
    N.rightMonomial x y (N.perm k) = if k = 2 then x else if k = 3 then y else 0 := by
  fin_cases k <;> simp [rightMonomial, N.perm.injective.eq_iff]

theorem pair_decomposition (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) :
    f = N.leftPart f + N.rightPart f := by
  ext k
  obtain ⟨k, rfl⟩ := N.perm.surjective k
  fin_cases k <;> simp [leftPart, rightPart]

@[simp] theorem weight_leftMonomial (N : NormalizedPairs B) (x y : ℕ) :
    weight B (N.leftMonomial x y) = N.u * (N.alpha * x + N.beta * y) := by
  simp only [leftMonomial, map_add, weight_single, N.weight0, N.weight1]
  ring

@[simp] theorem weight_rightMonomial (N : NormalizedPairs B) (x y : ℕ) :
    weight B (N.rightMonomial x y) = N.v * (N.gamma * x + N.delta * y) := by
  simp only [rightMonomial, map_add, weight_single, N.weight2, N.weight3]
  ring

theorem weight_split (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) :
    weight B f = N.u * N.leftValue f + N.v * N.rightValue f := by
  conv_lhs => rw [N.pair_decomposition f, map_add]
  simp [leftPart, rightPart, leftValue, rightValue]

theorem leftValue_zero_iff (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) :
    N.leftValue f = 0 ↔ N.RightSupported f := by
  have ha := N.alpha_ge
  have hb := N.beta_ge
  simp only [leftValue, RightSupported]
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨h, h'⟩; simp [h, h']

theorem rightValue_zero_iff (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) :
    N.rightValue f = 0 ↔ N.LeftSupported f := by
  have ha := N.gamma_ge
  have hb := N.delta_ge
  simp only [rightValue, LeftSupported]
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨h, h'⟩; simp [h, h']

theorem left_eq_part (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ)
    (hf : N.LeftSupported f) : f = N.leftPart f := by
  ext k
  obtain ⟨k, rfl⟩ := N.perm.surjective k
  fin_cases k <;> simp_all [LeftSupported, leftPart]

theorem right_eq_part (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ)
    (hf : N.RightSupported f) : f = N.rightPart f := by
  ext k
  obtain ⟨k, rfl⟩ := N.perm.surjective k
  fin_cases k <;> simp_all [RightSupported, rightPart]

/-- Every full-fiber monomial splits into two actual common-quotient contributions. -/
theorem fiber_quotient_split (N : NormalizedPairs B) (r : ℕ)
    (f : FactorizationFiber B (N.u * N.v * r)) :
    ∃ s t : ℕ, s ∈ N.T ∧ t ∈ N.T ∧ r = s + t ∧
      N.leftValue f.val = N.v * s ∧ N.rightValue f.val = N.u * t := by
  have hw := (N.weight_split f.val).symm.trans f.property
  have hvdvd : N.v ∣ N.leftValue f.val := N.uv_coprime.symm.dvd_of_dvd_mul_left (by
    apply (Nat.dvd_add_right (dvd_mul_right N.v (N.rightValue f.val))).mp
    rw [Nat.add_comm, hw]
    exact ⟨N.u * r, by ring⟩)
  have hudvd : N.u ∣ N.rightValue f.val := N.uv_coprime.dvd_of_dvd_mul_left (by
    apply (Nat.dvd_add_left (dvd_mul_right N.u (N.leftValue f.val))).mp
    rw [Nat.add_comm, hw]
    exact ⟨N.v * r, by ring⟩)
  obtain ⟨s, hs⟩ := hvdvd
  obtain ⟨t, ht⟩ := hudvd
  have hst : r = s + t := by
    rw [hs, ht] at hw
    have hp : 0 < N.u * N.v := Nat.mul_pos N.u_pos N.v_pos
    nlinarith
  refine ⟨s, t, ?_, ?_, hst, hs, ht⟩
  · exact (mem_twoGenerator N.alpha N.beta (N.v * s)).mpr
      ⟨f.val (N.perm 0), f.val (N.perm 1), hs.symm⟩
  · have hm : t ∈ N.rightQuotient := (mem_twoGenerator N.gamma N.delta (N.u * t)).mpr
      ⟨f.val (N.perm 2), f.val (N.perm 3), ht.symm⟩
    change t ∈ N.leftQuotient
    rw [N.common_quotient]
    exact hm

/-- Indecomposability rules out every factorization using both pairs. -/
theorem minimal_fiber_one_side (N : NormalizedPairs B) (r : ℕ)
    (hr : r ∈ minimalPositiveGenerators N.T)
    (f : FactorizationFiber B (N.u * N.v * r)) :
    N.LeftSupported f.val ∨ N.RightSupported f.val := by
  obtain ⟨s, t, hs, ht, hst, hX, hY⟩ := N.fiber_quotient_split r f
  by_cases hsz : s = 0
  · right
    apply (N.leftValue_zero_iff f.val).mp
    simp [hX, hsz]
  · left
    have htz : t = 0 := by
      by_contra ht0
      exact hr.2.2 ⟨s, t, hs, ht, Nat.pos_of_ne_zero hsz, Nat.pos_of_ne_zero ht0, hst⟩
    apply (N.rightValue_zero_iff f.val).mp
    simp [hY, htz]



/-- Positive common-quotient degrees have an interior vertex on each pair. -/
theorem pair_centers (N : NormalizedPairs B) (r : ℕ) (hr : r ∈ N.T) (hp : 0 < r) :
    ∃ L R : FactorizationFiber B (N.u * N.v * r),
      N.LeftSupported L.val ∧ N.RightSupported R.val ∧
      0 < L.val (N.perm 0) ∧ 0 < L.val (N.perm 1) ∧
      0 < R.val (N.perm 2) ∧ 0 < R.val (N.perm 3) := by
  obtain ⟨⟨a, b, ha, hb, hab⟩, ⟨c, e, hc, he, hce⟩⟩ := N.positive_representations r hr hp
  let L : FactorizationFiber B (N.u * N.v * r) := ⟨N.leftMonomial a b, by
    rw [N.weight_leftMonomial, ← hab]; ring⟩
  let R : FactorizationFiber B (N.u * N.v * r) := ⟨N.rightMonomial c e, by
    rw [N.weight_rightMonomial, ← hce]; ring⟩
  exact ⟨L, R, by simp [L, LeftSupported], by simp [R, RightSupported],
    by simpa [L] using ha, by simpa [L] using hb,
    by simpa [R] using hc, by simpa [R] using he⟩

theorem left_positive_coordinate (N : NormalizedPairs B) (d : ℕ) (hd : 0 < d)
    (f : FactorizationFiber B d) (hf : N.LeftSupported f.val) :
    0 < f.val (N.perm 0) ∨ 0 < f.val (N.perm 1) := by
  have hz := (N.rightValue_zero_iff f.val).mpr hf
  have hw := (N.weight_split f.val).symm.trans f.property
  by_contra hn
  push Not at hn
  have hzX : N.leftValue f.val = 0 := by
    dsimp [leftValue]
    rw [Nat.eq_zero_of_le_zero hn.1, Nat.eq_zero_of_le_zero hn.2]
    simp
  simp [hz, hzX] at hw
  omega

theorem right_positive_coordinate (N : NormalizedPairs B) (d : ℕ) (hd : 0 < d)
    (f : FactorizationFiber B d) (hf : N.RightSupported f.val) :
    0 < f.val (N.perm 2) ∨ 0 < f.val (N.perm 3) := by
  have hz := (N.leftValue_zero_iff f.val).mpr hf
  have hw := (N.weight_split f.val).symm.trans f.property
  by_contra hn
  push Not at hn
  have hzY : N.rightValue f.val = 0 := by
    dsimp [rightValue]
    rw [Nat.eq_zero_of_le_zero hn.1, Nat.eq_zero_of_le_zero hn.2]
    simp
  simp [hz, hzY] at hw
  omega

theorem left_component_eq (N : NormalizedPairs B) (d : ℕ) (hd : 0 < d)
    (f L : FactorizationFiber B d) (hf : N.LeftSupported f.val)
    (h0 : 0 < L.val (N.perm 0)) (h1 : 0 < L.val (N.perm 1)) :
    (fiberGraph B d).connectedComponentMk f = (fiberGraph B d).connectedComponentMk L := by
  rcases N.left_positive_coordinate d hd f hf with h | h
  · exact same_component_of_shared B d f L (N.perm 0) h h0
  · exact same_component_of_shared B d f L (N.perm 1) h h1

theorem right_component_eq (N : NormalizedPairs B) (d : ℕ) (hd : 0 < d)
    (f R : FactorizationFiber B d) (hf : N.RightSupported f.val)
    (h2 : 0 < R.val (N.perm 2)) (h3 : 0 < R.val (N.perm 3)) :
    (fiberGraph B d).connectedComponentMk f = (fiberGraph B d).connectedComponentMk R := by
  rcases N.right_positive_coordinate d hd f hf with h | h
  · exact same_component_of_shared B d f R (N.perm 2) h h2
  · exact same_component_of_shared B d f R (N.perm 3) h h3

theorem no_cross_adj (N : NormalizedPairs B) (d : ℕ) (f g : FactorizationFiber B d)
    (hf : N.LeftSupported f.val) (hg : N.RightSupported g.val) :
    ¬ (fiberGraph B d).Adj f g := by
  rintro ⟨_, k, hkf, hkg⟩
  obtain ⟨k, rfl⟩ := N.perm.surjective k
  change f.val (N.perm 2) = 0 ∧ f.val (N.perm 3) = 0 at hf
  change g.val (N.perm 0) = 0 ∧ g.val (N.perm 1) = 0 at hg
  fin_cases k <;> simp_all

/-- If no vertex uses both pairs, reachability preserves the pair side. -/
theorem reachable_preserves_left (N : NormalizedPairs B) (d : ℕ)
    (hsides : ∀ f : FactorizationFiber B d, N.LeftSupported f.val ∨ N.RightSupported f.val)
    (f g : FactorizationFiber B d) (hfg : (fiberGraph B d).Reachable f g)
    (hf : N.LeftSupported f.val) : N.LeftSupported g.val := by
  obtain ⟨w⟩ := hfg
  induction w with
  | nil => exact hf
  | @cons f z g h w ih =>
    apply ih
    rcases hsides z with hz | hz
    · exact hz
    · exact False.elim (N.no_cross_adj d f z hf hz h)

/-- An aligned Betti fiber is stated entirely in terms of its actual components. -/
def AlignedBetti (N : NormalizedPairs B) (d : ℕ) : Prop :=
  Betti B d ∧ ∃ C E : FiberComponent B d, C ≠ E ∧
    (∀ F : FiberComponent B d, F = C ∨ F = E) ∧
    componentSupport B d C = {N.perm 0, N.perm 1} ∧
    componentSupport B d E = {N.perm 2, N.perm 3}

/-- An indecomposable common-quotient degree has exactly the two aligned components. -/
theorem minimal_generator_aligned (N : NormalizedPairs B) (r : ℕ)
    (hr : r ∈ minimalPositiveGenerators N.T) : N.AlignedBetti (N.u * N.v * r) := by
  classical
  let d := N.u * N.v * r
  have hd : 0 < d := Nat.mul_pos (Nat.mul_pos N.u_pos N.v_pos) hr.2.1
  obtain ⟨L, R, hL, hR, hL0, hL1, hR2, hR3⟩ := N.pair_centers r hr.1 hr.2.1
  let C := (fiberGraph B d).connectedComponentMk L
  let E := (fiberGraph B d).connectedComponentMk R
  have hsides : ∀ f : FactorizationFiber B d,
      N.LeftSupported f.val ∨ N.RightSupported f.val := N.minimal_fiber_one_side r hr
  have hne : C ≠ E := by
    intro he
    have hp := N.reachable_preserves_left d hsides L R
      (SimpleGraph.ConnectedComponent.exact he) hL
    exact (Nat.ne_of_gt hR2) hp.1
  have hall (F : FiberComponent B d) : F = C ∨ F = E := by
    obtain ⟨f, hf⟩ := F.exists_rep
    rcases hsides f with h | h
    · left; exact hf.symm.trans (N.left_component_eq d hd f L h hL0 hL1)
    · right; exact hf.symm.trans (N.right_component_eq d hd f R h hR2 hR3)
  have hC : componentSupport B d C = {N.perm 0, N.perm 1} := by
    ext k
    constructor
    · intro hk
      obtain ⟨f, hf, hfk⟩ := (mem_componentSupport B d C k).mp hk
      have hside := N.reachable_preserves_left d hsides L f
        (SimpleGraph.ConnectedComponent.exact hf.symm) hL
      obtain ⟨k, rfl⟩ := N.perm.surjective k
      fin_cases k <;> simp_all [LeftSupported]
    · intro hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact (mem_componentSupport B d C _).mpr ⟨L, rfl, hL0⟩
      · exact (mem_componentSupport B d C _).mpr ⟨L, rfl, hL1⟩
  have hE : componentSupport B d E = {N.perm 2, N.perm 3} := by
    ext k
    constructor
    · intro hk
      obtain ⟨f, hf, hfk⟩ := (mem_componentSupport B d E k).mp hk
      have hside : N.RightSupported f.val := by
        rcases hsides f with h | h
        · have heq := N.left_component_eq d hd f L h hL0 hL1
          exact False.elim (hne (heq.symm.trans hf))
        · exact h
      obtain ⟨k, rfl⟩ := N.perm.surjective k
      fin_cases k <;> simp_all [RightSupported]
    · intro hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact (mem_componentSupport B d E _).mpr ⟨R, rfl, hR2⟩
      · exact (mem_componentSupport B d E _).mpr ⟨R, rfl, hR3⟩
  exact ⟨(betti_iff_nontrivial B d).mpr ⟨⟨C, E, hne⟩⟩, C, E, hne, hall, hC, hE⟩



/-- A vertex with a nonzero first-pair part connects to the first-pair interior
by extending that part with a first-pair representation of the remaining quotient. -/
theorem component_eq_left_of_value_pos (N : NormalizedPairs B) (r : ℕ) (hp : 0 < r)
    (f L : FactorizationFiber B (N.u * N.v * r))
    (hX : 0 < N.leftValue f.val)
    (h0 : 0 < L.val (N.perm 0)) (h1 : 0 < L.val (N.perm 1)) :
    (fiberGraph B (N.u * N.v * r)).connectedComponentMk f =
      (fiberGraph B (N.u * N.v * r)).connectedComponentMk L := by
  obtain ⟨s, t, hs, ht, hst, hfs, hft⟩ := N.fiber_quotient_split r f
  obtain ⟨a, b, hab⟩ := (mem_twoGenerator N.alpha N.beta (N.v * t)).mp ht
  let p : FactorizationFiber B (N.u * N.v * r) :=
    ⟨N.leftPart f.val + N.leftMonomial a b, by
      rw [map_add]
      rw [show weight B (N.leftPart f.val) = N.u * N.leftValue f.val by
        simp [leftPart, leftValue]]
      rw [N.weight_leftMonomial, ← hab, hfs, hst]
      ring⟩
  have hfp : (fiberGraph B (N.u * N.v * r)).connectedComponentMk f =
      (fiberGraph B (N.u * N.v * r)).connectedComponentMk p := by
    have hc : 0 < f.val (N.perm 0) ∨ 0 < f.val (N.perm 1) := by
      by_contra hn
      push Not at hn
      simp only [leftValue] at hX
      rw [Nat.eq_zero_of_le_zero hn.1, Nat.eq_zero_of_le_zero hn.2] at hX
      simp at hX
    rcases hc with hc | hc
    · apply same_component_of_shared B _ f p (N.perm 0) hc
      simp only [p, Finsupp.add_apply, leftPart, leftMonomial_apply]
      simp; omega
    · apply same_component_of_shared B _ f p (N.perm 1) hc
      simp only [p, Finsupp.add_apply, leftPart, leftMonomial_apply]
      simp; omega
  apply hfp.trans
  apply N.left_component_eq _ (Nat.mul_pos (Nat.mul_pos N.u_pos N.v_pos) hp) p L
    (by simp [p, LeftSupported, leftPart]) h0 h1

/-- The symmetric extension connects every nonzero second-pair part to its interior. -/
theorem component_eq_right_of_value_pos (N : NormalizedPairs B) (r : ℕ) (hp : 0 < r)
    (f R : FactorizationFiber B (N.u * N.v * r))
    (hY : 0 < N.rightValue f.val)
    (h2 : 0 < R.val (N.perm 2)) (h3 : 0 < R.val (N.perm 3)) :
    (fiberGraph B (N.u * N.v * r)).connectedComponentMk f =
      (fiberGraph B (N.u * N.v * r)).connectedComponentMk R := by
  obtain ⟨s, t, hs, ht, hst, hfs, hft⟩ := N.fiber_quotient_split r f
  have hsr : s ∈ N.rightQuotient := by
    rw [← N.common_quotient]
    exact hs
  obtain ⟨a, b, hab⟩ := (mem_twoGenerator N.gamma N.delta (N.u * s)).mp hsr
  let p : FactorizationFiber B (N.u * N.v * r) :=
    ⟨N.rightPart f.val + N.rightMonomial a b, by
      rw [map_add]
      rw [show weight B (N.rightPart f.val) = N.v * N.rightValue f.val by
        simp [rightPart, rightValue]]
      rw [N.weight_rightMonomial, ← hab, hft, hst]
      ring⟩
  have hfp : (fiberGraph B (N.u * N.v * r)).connectedComponentMk f =
      (fiberGraph B (N.u * N.v * r)).connectedComponentMk p := by
    have hc : 0 < f.val (N.perm 2) ∨ 0 < f.val (N.perm 3) := by
      by_contra hn
      push Not at hn
      simp only [rightValue] at hY
      rw [Nat.eq_zero_of_le_zero hn.1, Nat.eq_zero_of_le_zero hn.2] at hY
      simp at hY
    rcases hc with hc | hc
    · apply same_component_of_shared B _ f p (N.perm 2) hc
      simp only [p, Finsupp.add_apply, rightPart, rightMonomial_apply]
      simp; omega
    · apply same_component_of_shared B _ f p (N.perm 3) hc
      simp only [p, Finsupp.add_apply, rightPart, rightMonomial_apply]
      simp; omega
  apply hfp.trans
  apply N.right_component_eq _ (Nat.mul_pos (Nat.mul_pos N.u_pos N.v_pos) hp) p R
    (by simp [p, RightSupported, rightPart]) h2 h3

/-- A nontrivial common-quotient decomposition supplies an actual mixed vertex. -/
theorem decomposition_mixed_vertex (N : NormalizedPairs B) (s t : ℕ)
    (hs : s ∈ N.T) (ht : t ∈ N.T) (hsp : 0 < s) (htp : 0 < t) :
    ∃ f : FactorizationFiber B (N.u * N.v * (s + t)),
      0 < N.leftValue f.val ∧ 0 < N.rightValue f.val := by
  obtain ⟨a, b, ha, hb, hab⟩ := (N.positive_representations s hs hsp).1
  obtain ⟨c, e, hc, he, hce⟩ := (N.positive_representations t ht htp).2
  let f : FactorizationFiber B (N.u * N.v * (s + t)) :=
    ⟨N.leftMonomial a b + N.rightMonomial c e, by
      rw [map_add, N.weight_leftMonomial, N.weight_rightMonomial, ← hab, ← hce]
      ring⟩
  refine ⟨f, ?_, ?_⟩
  · have heq : N.leftValue f.val = N.v * s := by simp [f, leftValue, ← hab]
    rw [heq]; exact Nat.mul_pos N.v_pos hsp
  · have heq : N.rightValue f.val = N.u * t := by simp [f, rightValue, ← hce]
    rw [heq]; exact Nat.mul_pos N.u_pos htp

/-- Every factorization, including every mixed one, lies in the same actual
component at a decomposable common-quotient degree. -/
theorem decomposable_fiber_components_eq (N : NormalizedPairs B) (s t : ℕ)
    (hs : s ∈ N.T) (ht : t ∈ N.T) (hsp : 0 < s) (htp : 0 < t)
    (f g : FactorizationFiber B (N.u * N.v * (s + t))) :
    (fiberGraph B (N.u * N.v * (s + t))).connectedComponentMk f =
      (fiberGraph B (N.u * N.v * (s + t))).connectedComponentMk g := by
  have hp : 0 < s + t := by omega
  obtain ⟨L, R, hL, hR, hL0, hL1, hR2, hR3⟩ := N.pair_centers (s + t) (N.T.add_mem hs ht) hp
  obtain ⟨m, hmX, hmY⟩ := N.decomposition_mixed_vertex s t hs ht hsp htp
  have hLR := (N.component_eq_left_of_value_pos _ hp m L hmX hL0 hL1).symm.trans
    (N.component_eq_right_of_value_pos _ hp m R hmY hR2 hR3)
  have hall (z : FactorizationFiber B (N.u * N.v * (s + t))) :
      (fiberGraph B (N.u * N.v * (s + t))).connectedComponentMk z =
        (fiberGraph B (N.u * N.v * (s + t))).connectedComponentMk L := by
    by_cases hx : 0 < N.leftValue z.val
    · exact N.component_eq_left_of_value_pos _ hp z L hx hL0 hL1
    · have hz : N.RightSupported z.val := (N.leftValue_zero_iff z.val).mp (by omega)
      exact (N.right_component_eq _ (Nat.mul_pos (Nat.mul_pos N.u_pos N.v_pos) hp)
        z R hz hR2 hR3).trans hLR.symm
  exact (hall f).trans (hall g).symm

theorem decomposable_not_betti (N : NormalizedPairs B) (s t : ℕ)
    (hs : s ∈ N.T) (ht : t ∈ N.T) (hsp : 0 < s) (htp : 0 < t) :
    ¬ Betti B (N.u * N.v * (s + t)) := by
  intro hb
  obtain ⟨C, E, hne⟩ := @exists_pair_ne (FiberComponent B (N.u * N.v * (s + t)))
    ((betti_iff_nontrivial B _).mp hb)
  obtain ⟨f, hf⟩ := C.exists_rep
  obtain ⟨g, hg⟩ := E.exists_rep
  exact hne (hf.symm.trans ((N.decomposable_fiber_components_eq s t hs ht hsp htp f g).trans hg))

/-- Any positive Betti degree of the form u*v*r forces r to be a minimal generator. -/
theorem betti_common_degree_minimal (N : NormalizedPairs B) (r : ℕ)
    (hr : r ∈ N.T) (hb : Betti B (N.u * N.v * r)) :
    r ∈ minimalPositiveGenerators N.T := by
  have hd := betti_positive B _ hb
  refine ⟨hr, ?_, ?_⟩
  · by_contra hn
    have hz : r = 0 := by omega
    simp [hz] at hd
  · rintro ⟨s, t, hs, ht, hsp, htp, rfl⟩
    exact N.decomposable_not_betti s t hs ht hsp htp hb



theorem leftSupported_of_component (N : NormalizedPairs B) (d : ℕ)
    (C : FiberComponent B d) (hC : componentSupport B d C = {N.perm 0, N.perm 1})
    (f : FactorizationFiber B d) (hf : (fiberGraph B d).connectedComponentMk f = C) :
    N.LeftSupported f.val := by
  constructor
  · exact component_coordinate_zero B d C f hf (N.perm 2)
      (by simp [hC, N.perm.injective.eq_iff])
  · exact component_coordinate_zero B d C f hf (N.perm 3)
      (by simp [hC, N.perm.injective.eq_iff])

theorem rightSupported_of_component (N : NormalizedPairs B) (d : ℕ)
    (C : FiberComponent B d) (hC : componentSupport B d C = {N.perm 2, N.perm 3})
    (f : FactorizationFiber B d) (hf : (fiberGraph B d).connectedComponentMk f = C) :
    N.RightSupported f.val := by
  constructor
  · exact component_coordinate_zero B d C f hf (N.perm 0)
      (by simp [hC, N.perm.injective.eq_iff])
  · exact component_coordinate_zero B d C f hf (N.perm 1)
      (by simp [hC, N.perm.injective.eq_iff])

/-- Aligned supports force an actual common-quotient degree. -/
theorem aligned_common_degree (N : NormalizedPairs B) (d : ℕ) (hd : N.AlignedBetti d) :
    ∃ r : ℕ, r ∈ N.T ∧ d = N.u * N.v * r := by
  obtain ⟨hb, C, E, hne, hall, hC, hE⟩ := hd
  obtain ⟨f, hf⟩ := C.exists_rep
  obtain ⟨g, hg⟩ := E.exists_rep
  have hfside := N.leftSupported_of_component d C hC f hf
  have hgside := N.rightSupported_of_component d E hE g hg
  have hfzero := (N.rightValue_zero_iff f.val).mpr hfside
  have hgzero := (N.leftValue_zero_iff g.val).mpr hgside
  have huf : N.u * N.leftValue f.val = d := by
    simpa [hfzero] using (N.weight_split f.val).symm.trans f.property
  have hvg : N.v * N.rightValue g.val = d := by
    simpa [hgzero] using (N.weight_split g.val).symm.trans g.property
  have hdvd : N.u * N.v ∣ d := N.uv_coprime.mul_dvd_of_dvd_of_dvd
    ⟨N.leftValue f.val, huf.symm⟩ ⟨N.rightValue g.val, hvg.symm⟩
  obtain ⟨r, hr⟩ := hdvd
  refine ⟨r, ?_, hr⟩
  have hvr : N.v * r = N.leftValue f.val := by
    have := N.u_pos
    nlinarith [huf, hr]
  exact (mem_twoGenerator N.alpha N.beta (N.v * r)).mpr
    ⟨f.val (N.perm 0), f.val (N.perm 1), hvr⟩

/-- Forward aligned direction, retaining the exact minimal-generator witness. -/
theorem aligned_degree_minimal (N : NormalizedPairs B) (d : ℕ) (hd : N.AlignedBetti d) :
    ∃ r ∈ minimalPositiveGenerators N.T, d = N.u * N.v * r := by
  obtain ⟨r, hr, he⟩ := N.aligned_common_degree d hd
  exact ⟨r, N.betti_common_degree_minimal r hr (he ▸ hd.1), he⟩

/-- Appendix B aligned Betti characterization in both directions, on the actual graph. -/
theorem aligned_betti_iff (N : NormalizedPairs B) (d : ℕ) :
    N.AlignedBetti d ↔ ∃ r ∈ minimalPositiveGenerators N.T, d = N.u * N.v * r := by
  constructor
  · exact N.aligned_degree_minimal d
  · rintro ⟨r, hr, rfl⟩
    exact N.minimal_generator_aligned r hr

/-- At every common-multiple degree, actual Betti behavior is precisely
indecomposability in the common quotient. -/
theorem betti_common_multiple_iff (N : NormalizedPairs B) (r : ℕ) :
    Betti B (N.u * N.v * r) ↔ r ∈ minimalPositiveGenerators N.T := by
  constructor
  · intro hb
    have hn := (betti_iff_nontrivial B _).mp hb
    let := hn
    obtain ⟨C, _, _⟩ := exists_pair_ne (FiberComponent B (N.u * N.v * r))
    obtain ⟨f, hf⟩ := C.exists_rep
    obtain ⟨s, t, hs, ht, hst, _, _⟩ := N.fiber_quotient_split r f
    apply N.betti_common_degree_minimal r _ hb
    rw [hst]
    exact N.T.add_mem hs ht
  · intro hr
    exact (N.minimal_generator_aligned r hr).1

theorem aligned_componentCount_two (N : NormalizedPairs B) (d : ℕ)
    (hd : N.AlignedBetti d) : componentCount B d = 2 := by
  classical
  let := Fintype.ofFinite (FiberComponent B d)
  obtain ⟨_, C, E, hne, hall, _, _⟩ := hd
  have hset : (Finset.univ : Finset (FiberComponent B d)) = {C, E} := by
    ext F
    simpa only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff] using hall F
  simp [componentCount, Nat.card_eq_fintype_card, ← Finset.card_univ, hset, hne]

end NormalizedPairs
end NS25Lean.L4A

