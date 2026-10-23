import NS25Lean.P2SectorCInnerColonR19

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR20

open L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR3
  L5A2C4OR4 L5A2C4OR5 L5A2C4OR6 L5A2C4OR19

variable {Gamma : NumericalSemigroup}

private theorem grid_mem_H (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r u v : ℕ) : normalizedGrid B e r u v ∈ routingH B e := by
  have ha : routingA B e ∈ routingH B e := by
    change routingA B e ∈ FourGeneratedBridge.generatedThree
      (routingA B e) (routingB B e) (routingC B e)
    exact AddSubmonoid.subset_closure (by simp)
  have hr := (routingH B e).toAddSubmonoid.nsmul_mem ha r
  have hu := (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e) u
  have hv := (routingH B e).toAddSubmonoid.nsmul_mem (routingHC B e) v
  simpa [normalizedGrid, nsmul_eq_mul, Nat.add_assoc] using
    (routingH B e).toAddSubmonoid.add_mem
      ((routingH B e).toAddSubmonoid.add_mem hr hu) hv

/-- A positive a-subtraction from a genuine canonical L-bottom cannot stay
in H. Canonicality is derived from frozen R6, never imposed off-domain. -/
theorem canonical_no_positive_a_subtraction
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {P Q z x : ℕ}
    (hdom : HerzogLShapeDomain HD P Q) (hz : 0 < z)
    (heq : x + z * routingA B e = P * routingB B e + Q * routingC B e) :
    x ∉ routingH B e := by
  intro hx
  let : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hmod := congrArg (fun n : ℕ => (n : ZMod (routingA B e))) heq
  have hxmod : (x : ZMod (routingA B e)) = gridResidue B e P Q := by
    simpa [gridResidue] using hmod
  have hmin := (routingH B e).asRelativeIdeal.aperyRepresentative_le
    (routingA B e) (gridResidue B e P Q)
    (show (x : ℤ) ∈ (routingH B e).asRelativeIdeal from ⟨x, hx, rfl⟩)
    (by exact_mod_cast hxmod)
  have hcan := herzogLShapeCanonicality B e HD P Q hdom
  change (normalizedGrid B e 0 P Q : ℤ) =
    (routingH B e).asRelativeIdeal.aperyRepresentative
      (routingA B e) (gridResidue B e P Q) at hcan
  rw [← hcan] at hmin
  have hle : P * routingB B e + Q * routingC B e ≤ x := by
    simpa [normalizedGrid] using (show normalizedGrid B e 0 P Q ≤ x by exact_mod_cast hmin)
  have ha := routingA_pos B e
  nlinarith

/-- T3 inner forward inclusion: central and both wraps yield explicit
nonnegative H-summands; the remaining canonical case contradicts Apéry
minimality. The extended pair is not assumed canonical. -/
theorem inner_colon_forward_generation
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d : ℕ}
    (_hn : 0 < n) (_hi0 : 0 < i) (_hi : i < cr12 HD)
    (_hj0 : 0 < j) (_hj : j < cr13 HD) (_hd : 0 < d)
    (hdk : d < cr21 HD) (hdl : d < cr31 HD)
    (heq : n * routingM B e + d * routingA B e =
      i * routingB B e + j * routingC B e) :
    positiveReturnPiece (routingH B e) (routingM B e) n ⊆
      hGeneratedSet (routingH B e) (innerColonGenerators B e HD i j d) := by
  rintro x ⟨hxH, _, h, hh, hx⟩
  obtain ⟨r, u, v, hfac⟩ := routingH_factorization B e hh
  rw [hfac] at hx
  have hs := coherent_coefficients B e HD
  have hr := coherent_normalized_relations B e HD
  by_cases ha : d ≤ r
  · have hD := congrArg (fun z => z * routingA B e) (Nat.sub_add_cancel ha)
    simp only [Nat.add_mul] at hD
    refine ⟨normalizedGrid B e 0 i j, Or.inl rfl,
      normalizedGrid B e (r-d) u v, grid_mem_H B e _ _ _, ?_⟩
    simp only [normalizedGrid, zero_mul, zero_add]
    nlinarith only [heq, hx, hD]
  · have hrd : r < d := by omega
    by_cases hc : cr12 HD ≤ i+u ∧ cr13 HD ≤ j+v
    · have hD := congrArg (fun z => z * routingA B e)
        (show c1 B e - d + d = c1 B e by omega)
      have hP := congrArg (fun z => z * routingB B e) (Nat.sub_add_cancel hc.1)
      have hQ := congrArg (fun z => z * routingC B e) (Nat.sub_add_cancel hc.2)
      simp only [Nat.add_mul] at hD hP hQ
      refine ⟨normalizedGrid B e (c1 B e-d) 0 0,
        Or.inr (Or.inr (Or.inr rfl)),
        normalizedGrid B e r (i+u-cr12 HD) (j+v-cr13 HD), grid_mem_H B e _ _ _, ?_⟩
      simp only [normalizedGrid, zero_mul, add_zero]
      nlinarith only [heq, hx, hr.1, hD, hP, hQ]
    · by_cases hb : c2 B e ≤ i+u
      · have hD := congrArg (fun z => z * routingA B e)
          (show cr21 HD-d+d=cr21 HD by omega)
        have hP := congrArg (fun z => z * routingB B e) (Nat.sub_add_cancel hb)
        simp only [Nat.add_mul] at hD hP
        refine ⟨normalizedGrid B e (cr21 HD-d) 0 (j+cr23 HD),
          Or.inr (Or.inr (Or.inl rfl)),
          normalizedGrid B e r (i+u-c2 B e) v, grid_mem_H B e _ _ _, ?_⟩
        simp only [normalizedGrid, zero_mul, Nat.add_mul]
        nlinarith only [heq, hx, hr.2.1, hD, hP]
      · by_cases hcw : c3 B e ≤ j+v
        · have hD := congrArg (fun z => z * routingA B e)
            (show cr31 HD-d+d=cr31 HD by omega)
          have hQ := congrArg (fun z => z * routingC B e) (Nat.sub_add_cancel hcw)
          simp only [Nat.add_mul] at hD hQ
          refine ⟨normalizedGrid B e (cr31 HD-d) (i+cr32 HD) 0,
            Or.inr (Or.inl rfl),
            normalizedGrid B e r u (j+v-c3 B e), grid_mem_H B e _ _ _, ?_⟩
          simp only [normalizedGrid, zero_mul, add_zero, Nat.add_mul]
          nlinarith only [heq, hx, hr.2.2, hD, hQ]
        · have hdom : HerzogLShapeDomain HD (i+u) (j+v) := by
            exact ⟨by omega, by omega, by omega⟩
          have hD := congrArg (fun z => z * routingA B e)
            (Nat.sub_add_cancel (Nat.le_of_lt hrd))
          simp only [Nat.add_mul] at hD
          have hbottom : x + (d-r)*routingA B e =
              (i+u)*routingB B e + (j+v)*routingC B e := by
            simp only [Nat.add_mul]
            nlinarith only [heq, hx, hD]
          exact (canonical_no_positive_a_subtraction B e HD hdom
            (by omega) hbottom hxH).elim

/-- T3 inner equality combines the new forward direction with the frozen
R19 reverse direction; neither inclusion is an input premise. -/
theorem inner_colon_exact_generation
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d : ℕ}
    (hn : 0 < n) (hi0 : 0 < i) (hi : i < cr12 HD)
    (hj0 : 0 < j) (hj : j < cr13 HD) (hd : 0 < d)
    (hdk : d < cr21 HD) (hdl : d < cr31 HD)
    (heq : n * routingM B e + d * routingA B e =
      i * routingB B e + j * routingC B e) :
    positiveReturnPiece (routingH B e) (routingM B e) n =
      hGeneratedSet (routingH B e) (innerColonGenerators B e HD i j d) :=
  Set.Subset.antisymm
    (inner_colon_forward_generation B e HD hn hi0 hi hj0 hj hd hdk hdl heq)
    (inner_colon_reverse_inclusion B e HD hn hi hj hdk hdl heq)

/-- The three actual degree generators for a top preprincipal colon. -/
def topColonGenerators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j d : ℕ) : Set ℕ :=
  {g | g = normalizedGrid B e 0 i j ∨
    g = normalizedGrid B e (cr31 HD-d) (i+cr32 HD) 0 ∨
    g = normalizedGrid B e (c1 B e-d) 0 (j-cr13 HD)}

/-- The three actual degree generators for a right preprincipal colon. -/
def rightColonGenerators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j d : ℕ) : Set ℕ :=
  {g | g = normalizedGrid B e 0 i j ∨
    g = normalizedGrid B e (cr21 HD-d) 0 (j+cr23 HD) ∨
    g = normalizedGrid B e (c1 B e-d) (i-cr12 HD) 0}

private theorem generated_return_subset
    (H : NumericalSemigroup) (m n : ℕ) (G : Set ℕ)
    (hG : ∀ g ∈ G, g ∈ positiveReturnPiece H m n) :
    hGeneratedSet H G ⊆ positiveReturnPiece H m n := by
  rintro x ⟨g, hg, h, hh, rfl⟩
  obtain ⟨hgH, hn, t, ht, hgt⟩ := hG g hg
  refine ⟨H.toAddSubmonoid.add_mem hgH hh, hn,
    t+h, H.toAddSubmonoid.add_mem ht hh, ?_⟩
  rw [hgt]
  omega

/-- Every top generator is an actual return, with explicit H difference. -/
theorem topColonGenerators_mem_returnPiece
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d : ℕ}
    (hn : 0 < n) (hi : i < cr12 HD) (hqj : cr13 HD ≤ j)
    (hj : j < c3 B e) (hdl : d < cr31 HD)
    (heq : n * routingM B e + d * routingA B e =
      i * routingB B e + j * routingC B e) :
    ∀ g ∈ topColonGenerators B e HD i j d,
      g ∈ positiveReturnPiece (routingH B e) (routingM B e) n := by
  have hs := coherent_coefficients B e HD
  have hr := coherent_normalized_relations B e HD
  intro g hg
  rcases hg with rfl | rfl | rfl
  · refine ⟨grid_mem_H B e _ _ _, hn, normalizedGrid B e d 0 0,
      grid_mem_H B e _ _ _, ?_⟩
    simpa [normalizedGrid] using heq.symm
  · have hD := congrArg (fun z => z * routingA B e)
      (show cr31 HD-d+d=cr31 HD by omega)
    have hJ := congrArg (fun z => z * routingC B e)
      (Nat.sub_add_cancel (Nat.le_of_lt hj))
    simp only [Nat.add_mul] at hD hJ
    refine ⟨grid_mem_H B e _ _ _, hn, normalizedGrid B e 0 0 (c3 B e-j),
      grid_mem_H B e _ _ _, ?_⟩
    simp only [normalizedGrid, zero_mul, zero_add, add_zero, Nat.add_mul]
    nlinarith only [heq, hr.2.2, hD, hJ]
  · have hD := congrArg (fun z => z * routingA B e)
      (show c1 B e-d+d=c1 B e by omega)
    have hI := congrArg (fun z => z * routingB B e)
      (Nat.sub_add_cancel (Nat.le_of_lt hi))
    have hJ := congrArg (fun z => z * routingC B e) (Nat.sub_add_cancel hqj)
    simp only [Nat.add_mul] at hD hI hJ
    refine ⟨grid_mem_H B e _ _ _, hn, normalizedGrid B e 0 (cr12 HD-i) 0,
      grid_mem_H B e _ _ _, ?_⟩
    simp only [normalizedGrid, zero_mul, zero_add, add_zero]
    nlinarith only [heq, hr.1, hD, hI, hJ]

/-- Every right generator is an actual return, with explicit H difference. -/
theorem rightColonGenerators_mem_returnPiece
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d : ℕ}
    (hn : 0 < n) (hpi : cr12 HD ≤ i) (hi : i < c2 B e)
    (hj : j < cr13 HD) (hdk : d < cr21 HD)
    (heq : n * routingM B e + d * routingA B e =
      i * routingB B e + j * routingC B e) :
    ∀ g ∈ rightColonGenerators B e HD i j d,
      g ∈ positiveReturnPiece (routingH B e) (routingM B e) n := by
  have hs := coherent_coefficients B e HD
  have hr := coherent_normalized_relations B e HD
  intro g hg
  rcases hg with rfl | rfl | rfl
  · refine ⟨grid_mem_H B e _ _ _, hn, normalizedGrid B e d 0 0,
      grid_mem_H B e _ _ _, ?_⟩
    simpa [normalizedGrid] using heq.symm
  · have hD := congrArg (fun z => z * routingA B e)
      (show cr21 HD-d+d=cr21 HD by omega)
    have hI := congrArg (fun z => z * routingB B e)
      (Nat.sub_add_cancel (Nat.le_of_lt hi))
    simp only [Nat.add_mul] at hD hI
    refine ⟨grid_mem_H B e _ _ _, hn, normalizedGrid B e 0 (c2 B e-i) 0,
      grid_mem_H B e _ _ _, ?_⟩
    simp only [normalizedGrid, zero_mul, zero_add, add_zero, Nat.add_mul]
    nlinarith only [heq, hr.2.1, hD, hI]
  · have hD := congrArg (fun z => z * routingA B e)
      (show c1 B e-d+d=c1 B e by omega)
    have hI := congrArg (fun z => z * routingB B e) (Nat.sub_add_cancel hpi)
    have hJ := congrArg (fun z => z * routingC B e)
      (Nat.sub_add_cancel (Nat.le_of_lt hj))
    simp only [Nat.add_mul] at hD hI hJ
    refine ⟨grid_mem_H B e _ _ _, hn, normalizedGrid B e 0 0 (cr13 HD-j),
      grid_mem_H B e _ _ _, ?_⟩
    simp only [normalizedGrid, zero_mul, zero_add, add_zero]
    nlinarith only [heq, hr.1, hD, hI, hJ]

/-- Top forward inclusion: central whenever P≥p, otherwise only c-wrap
can leave L. All residual coefficients are nonnegative. -/
theorem top_colon_forward_generation
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d : ℕ}
    (_hn : 0 < n) (_hi0 : 0 < i) (_hi : i < cr12 HD)
    (hqj : cr13 HD ≤ j) (_hj : j < c3 B e) (_hd : 0 < d)
    (hdl : d < cr31 HD)
    (heq : n * routingM B e + d * routingA B e =
      i * routingB B e + j * routingC B e) :
    positiveReturnPiece (routingH B e) (routingM B e) n ⊆
      hGeneratedSet (routingH B e) (topColonGenerators B e HD i j d) := by
  rintro x ⟨hxH, _, h, hh, hx⟩
  obtain ⟨r, u, v, hfac⟩ := routingH_factorization B e hh
  rw [hfac] at hx
  have hs := coherent_coefficients B e HD
  have hr := coherent_normalized_relations B e HD
  by_cases ha : d ≤ r
  · have hD := congrArg (fun z => z * routingA B e) (Nat.sub_add_cancel ha)
    simp only [Nat.add_mul] at hD
    refine ⟨normalizedGrid B e 0 i j, Or.inl rfl,
      normalizedGrid B e (r-d) u v, grid_mem_H B e _ _ _, ?_⟩
    simp only [normalizedGrid, zero_mul, zero_add]
    nlinarith only [heq, hx, hD]
  · have hrd : r < d := by omega
    by_cases hc : cr12 HD ≤ i+u
    · have hD := congrArg (fun z => z * routingA B e)
        (show c1 B e-d+d=c1 B e by omega)
      have hP := congrArg (fun z => z * routingB B e) (Nat.sub_add_cancel hc)
      have hJ := congrArg (fun z => z * routingC B e) (Nat.sub_add_cancel hqj)
      simp only [Nat.add_mul] at hD hP hJ
      refine ⟨normalizedGrid B e (c1 B e-d) 0 (j-cr13 HD),
        Or.inr (Or.inr rfl),
        normalizedGrid B e r (i+u-cr12 HD) v, grid_mem_H B e _ _ _, ?_⟩
      simp only [normalizedGrid, zero_mul]
      nlinarith only [heq, hx, hr.1, hD, hP, hJ]
    · by_cases hw : c3 B e ≤ j+v
      · have hD := congrArg (fun z => z * routingA B e)
          (show cr31 HD-d+d=cr31 HD by omega)
        have hQ := congrArg (fun z => z * routingC B e) (Nat.sub_add_cancel hw)
        simp only [Nat.add_mul] at hD hQ
        refine ⟨normalizedGrid B e (cr31 HD-d) (i+cr32 HD) 0,
          Or.inr (Or.inl rfl),
          normalizedGrid B e r u (j+v-c3 B e), grid_mem_H B e _ _ _, ?_⟩
        simp only [normalizedGrid, zero_mul, add_zero, Nat.add_mul]
        nlinarith only [heq, hx, hr.2.2, hD, hQ]
      · have hdom : HerzogLShapeDomain HD (i+u) (j+v) :=
          ⟨by omega, by omega, Or.inl (by omega)⟩
        have hD := congrArg (fun z => z * routingA B e)
          (Nat.sub_add_cancel (Nat.le_of_lt hrd))
        simp only [Nat.add_mul] at hD
        have hbottom : x + (d-r)*routingA B e =
            (i+u)*routingB B e + (j+v)*routingC B e := by
          simp only [Nat.add_mul]
          nlinarith only [heq, hx, hD]
        exact (canonical_no_positive_a_subtraction B e HD hdom
          (by omega) hbottom hxH).elim

/-- Right forward inclusion, with the symmetric central/b-wrap split. -/
theorem right_colon_forward_generation
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d : ℕ}
    (_hn : 0 < n) (hpi : cr12 HD ≤ i) (_hi : i < c2 B e)
    (_hj0 : 0 < j) (_hj : j < cr13 HD) (_hd : 0 < d)
    (hdk : d < cr21 HD)
    (heq : n * routingM B e + d * routingA B e =
      i * routingB B e + j * routingC B e) :
    positiveReturnPiece (routingH B e) (routingM B e) n ⊆
      hGeneratedSet (routingH B e) (rightColonGenerators B e HD i j d) := by
  rintro x ⟨hxH, _, h, hh, hx⟩
  obtain ⟨r, u, v, hfac⟩ := routingH_factorization B e hh
  rw [hfac] at hx
  have hs := coherent_coefficients B e HD
  have hr := coherent_normalized_relations B e HD
  by_cases ha : d ≤ r
  · have hD := congrArg (fun z => z * routingA B e) (Nat.sub_add_cancel ha)
    simp only [Nat.add_mul] at hD
    refine ⟨normalizedGrid B e 0 i j, Or.inl rfl,
      normalizedGrid B e (r-d) u v, grid_mem_H B e _ _ _, ?_⟩
    simp only [normalizedGrid, zero_mul, zero_add]
    nlinarith only [heq, hx, hD]
  · have hrd : r < d := by omega
    by_cases hc : cr13 HD ≤ j+v
    · have hD := congrArg (fun z => z * routingA B e)
        (show c1 B e-d+d=c1 B e by omega)
      have hI := congrArg (fun z => z * routingB B e) (Nat.sub_add_cancel hpi)
      have hQ := congrArg (fun z => z * routingC B e) (Nat.sub_add_cancel hc)
      simp only [Nat.add_mul] at hD hI hQ
      refine ⟨normalizedGrid B e (c1 B e-d) (i-cr12 HD) 0,
        Or.inr (Or.inr rfl),
        normalizedGrid B e r u (j+v-cr13 HD), grid_mem_H B e _ _ _, ?_⟩
      simp only [normalizedGrid, zero_mul, add_zero]
      nlinarith only [heq, hx, hr.1, hD, hI, hQ]
    · by_cases hw : c2 B e ≤ i+u
      · have hD := congrArg (fun z => z * routingA B e)
          (show cr21 HD-d+d=cr21 HD by omega)
        have hP := congrArg (fun z => z * routingB B e) (Nat.sub_add_cancel hw)
        simp only [Nat.add_mul] at hD hP
        refine ⟨normalizedGrid B e (cr21 HD-d) 0 (j+cr23 HD),
          Or.inr (Or.inl rfl),
          normalizedGrid B e r (i+u-c2 B e) v, grid_mem_H B e _ _ _, ?_⟩
        simp only [normalizedGrid, zero_mul, Nat.add_mul]
        nlinarith only [heq, hx, hr.2.1, hD, hP]
      · have hdom : HerzogLShapeDomain HD (i+u) (j+v) :=
          ⟨by omega, by omega, Or.inr (by omega)⟩
        have hD := congrArg (fun z => z * routingA B e)
          (Nat.sub_add_cancel (Nat.le_of_lt hrd))
        simp only [Nat.add_mul] at hD
        have hbottom : x + (d-r)*routingA B e =
            (i+u)*routingB B e + (j+v)*routingC B e := by
          simp only [Nat.add_mul]
          nlinarith only [heq, hx, hD]
        exact (canonical_no_positive_a_subtraction B e HD hdom
          (by omega) hbottom hxH).elim

theorem top_colon_exact_generation
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d : ℕ}
    (hn : 0 < n) (hi0 : 0 < i) (hi : i < cr12 HD)
    (hqj : cr13 HD ≤ j) (hj : j < c3 B e) (hd : 0 < d)
    (hdl : d < cr31 HD)
    (heq : n * routingM B e + d * routingA B e =
      i * routingB B e + j * routingC B e) :
    positiveReturnPiece (routingH B e) (routingM B e) n =
      hGeneratedSet (routingH B e) (topColonGenerators B e HD i j d) :=
  Set.Subset.antisymm
    (top_colon_forward_generation B e HD hn hi0 hi hqj hj hd hdl heq)
    (generated_return_subset _ _ _ _
      (topColonGenerators_mem_returnPiece B e HD hn hi hqj hj hdl heq))

theorem right_colon_exact_generation
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d : ℕ}
    (hn : 0 < n) (hpi : cr12 HD ≤ i) (hi : i < c2 B e)
    (hj0 : 0 < j) (hj : j < cr13 HD) (hd : 0 < d)
    (hdk : d < cr21 HD)
    (heq : n * routingM B e + d * routingA B e =
      i * routingB B e + j * routingC B e) :
    positiveReturnPiece (routingH B e) (routingM B e) n =
      hGeneratedSet (routingH B e) (rightColonGenerators B e HD i j d) :=
  Set.Subset.antisymm
    (right_colon_forward_generation B e HD hn hpi hi hj0 hj hd hdk heq)
    (generated_return_subset _ _ _ _
      (rightColonGenerators_mem_returnPiece B e HD hn hpi hi hj hdk heq))

/-- Source-exact selection among the three T2 colon lists. -/
def preprincipalColonGenerators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j d : ℕ) : Set ℕ :=
  if i < cr12 HD then
    if j < cr13 HD then innerColonGenerators B e HD i j d
    else topColonGenerators B e HD i j d
  else rightColonGenerators B e HD i j d

/-- The exact, exhaustive T2 shape/depth alternatives, not generatedness. -/
def PreprincipalCases (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j d : ℕ) : Prop :=
  (0 < i ∧ i < cr12 HD ∧ 0 < j ∧ j < cr13 HD ∧
    d < cr21 HD ∧ d < cr31 HD) ∨
  (0 < i ∧ i < cr12 HD ∧ cr13 HD ≤ j ∧ j < c3 B e ∧ d < cr31 HD) ∨
  (cr12 HD ≤ i ∧ i < c2 B e ∧ 0 < j ∧ j < cr13 HD ∧ d < cr21 HD)

/-- T3 combined exactness consumes only the actual T2 numerical case data,
and proves generation rather than taking it as an assumption. -/
theorem colon_piece_exact
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (heq : n * routingM B e + d * routingA B e =
      i * routingB B e + j * routingC B e)
    (hcases : PreprincipalCases B e HD i j d) :
    positiveReturnPiece (routingH B e) (routingM B e) n =
      hGeneratedSet (routingH B e) (preprincipalColonGenerators B e HD i j d) := by
  rcases hcases with h | h | h
  · simpa [preprincipalColonGenerators, h.2.1, h.2.2.2.1] using
      inner_colon_exact_generation B e HD hn h.1 h.2.1
        h.2.2.1 h.2.2.2.1 hd h.2.2.2.2.1 h.2.2.2.2.2 heq
  · simpa [preprincipalColonGenerators, h.2.1, Nat.not_lt.mpr h.2.2.1] using
      top_colon_exact_generation B e HD hn h.1 h.2.1
        h.2.2.1 h.2.2.2.1 hd h.2.2.2.2 heq
  · simpa [preprincipalColonGenerators, Nat.not_lt.mpr h.1] using
      right_colon_exact_generation B e HD hn h.1 h.2.1
        h.2.2.1 h.2.2.2.1 hd h.2.2.2.2 heq

/-- Actual mixed-notch adapter: frozen R19 constructs the canonical T2
coordinates and all case/depth data on the same role-normalized packet.
No numerical gate, generation, or resource map is supplied by the caller. -/
theorem actual_preprincipal_colon_piece_exact {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hMixed : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hNotch : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    {n : ℕ} (hn : 0 < n)
    (hpre : n < firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e)
      (routingM_pos P.M.base R.e)) :
    ∃ i j d : ℕ, HerzogLShapeDomain R.HD i j ∧ 0 < d ∧
      n * routingM P.M.base R.e + d * routingA P.M.base R.e =
        i * routingB P.M.base R.e + j * routingC P.M.base R.e ∧
      PreprincipalCases P.M.base R.e R.HD i j d ∧
      positiveReturnPiece (routingH P.M.base R.e) (routingM P.M.base R.e) n =
        hGeneratedSet (routingH P.M.base R.e)
          (preprincipalColonGenerators P.M.base R.e R.HD i j d) := by
  obtain ⟨i, j, d, hdom, hd, heq, hcases⟩ :=
    actual_mixed_notch_preprincipal R hMixed hNotch hn hpre
  exact ⟨i, j, d, hdom, hd, heq, hcases,
    colon_piece_exact P.M.base R.e R.HD hn hd heq hcases⟩

/-- T4 starts with literal exponent triples, distinguished from H degrees. -/
abbrev Monomial := ℕ × ℕ × ℕ

def monomialDegree (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (z : Monomial) : ℕ := normalizedGrid B e z.1 z.2.1 z.2.2

def colonMonomials (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j d : ℕ) : Set Monomial :=
  if i < cr12 HD then
    if j < cr13 HD then
      {z | z = (0,i,j) ∨ z = (cr31 HD-d,i+cr32 HD,0) ∨
        z = (cr21 HD-d,0,j+cr23 HD) ∨ z = (c1 B e-d,0,0)}
    else
      {z | z = (0,i,j) ∨ z = (cr31 HD-d,i+cr32 HD,0) ∨
        z = (c1 B e-d,0,j-cr13 HD)}
  else
    {z | z = (0,i,j) ∨ z = (cr21 HD-d,0,j+cr23 HD) ∨
      z = (c1 B e-d,i-cr12 HD,0)}

private theorem colonMonomials_degree_mem
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j d : ℕ) {z : Monomial}
    (hz : z ∈ colonMonomials B e HD i j d) :
    monomialDegree B e z ∈ preprincipalColonGenerators B e HD i j d := by
  by_cases hi : i < cr12 HD
  · by_cases hj : j < cr13 HD
    · simp only [colonMonomials, hi, hj, ite_true, Set.mem_ofPred_eq] at hz
      rcases hz with rfl | rfl | rfl | rfl <;>
        simp [monomialDegree, preprincipalColonGenerators, hi, hj, innerColonGenerators]
    · simp only [colonMonomials, hi, hj, ite_true, ite_false, Set.mem_ofPred_eq] at hz
      rcases hz with rfl | rfl | rfl <;>
        simp [monomialDegree, preprincipalColonGenerators, hi, hj, topColonGenerators]
  · simp only [colonMonomials, hi, ite_false, Set.mem_ofPred_eq] at hz
    rcases hz with rfl | rfl | rfl <;>
      simp [monomialDegree, preprincipalColonGenerators, hi, rightColonGenerators]

/-- The exact initial M-generator list of the authority: x^H0, T3 entries
for all preprincipal indices, and P/PB/PC at the actual first principal.
This definition contains no cut-membership or generatedness conclusion. -/
def canonicalIdealGenerators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Set Monomial :=
  {z | z = (H0 B e,0,0) ∨
    (∃ n i j d : ℕ, 0 < n ∧
      n < firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e) ∧
      0 < d ∧ n * routingM B e + d * routingA B e =
        i * routingB B e + j * routingC B e ∧
      PreprincipalCases B e HD i j d ∧ z ∈ colonMonomials B e HD i j d) ∨
    (∃ delta U V : ℕ, HerzogLShapeDomain HD U V ∧
      firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e) * routingM B e =
        normalizedGrid B e delta U V ∧
      (z = (delta,U,V) ∨ z = (delta+cr21 HD,0,V+cr23 HD) ∨
        z = (delta+cr31 HD,U+cr32 HD,0)))}

def monomialClosure (G : Set Monomial) : Set Monomial :=
  {z | ∃ g ∈ G, g.1 ≤ z.1 ∧ g.2.1 ≤ z.2.1 ∧ g.2.2 ≤ z.2.2}

private theorem cut_add_H {H : NumericalSemigroup} {m x h : ℕ}
    (hx : x ∈ cyclicCut H m) (hh : h ∈ H) : x+h ∈ cyclicCut H m := by
  obtain ⟨hxH,n,hn,t,ht,heq⟩ := hx
  refine ⟨H.toAddSubmonoid.add_mem hxH hh, n, hn, t+h,
    H.toAddSubmonoid.add_mem ht hh, ?_⟩
  rw [heq]
  omega

/-- T4 soundness of every initial generator, including the non-source PB
and PC degrees. Being a true cut is not confused with being a source. -/
theorem canonicalIdealGenerators_degree_mem_cut
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {z : Monomial}
    (hz : z ∈ canonicalIdealGenerators B e HD) :
    monomialDegree B e z ∈ cyclicCut (routingH B e) (routingM B e) := by
  rcases hz with rfl | hcolon | hprincipal
  · apply (actual_cyclicCut_iff_routingI B e _).mpr
    exact (normalizedGrid_mem_iff_eta_le B e (H0 B e) 0 0).mpr (le_refl _)
  · obtain ⟨n,i,j,d,hn,_hpre,hd,heq,hcases,hz⟩ := hcolon
    have hdeg := colonMonomials_degree_mem B e HD i j d hz
    have hg : monomialDegree B e z ∈ hGeneratedSet (routingH B e)
        (preprincipalColonGenerators B e HD i j d) :=
      ⟨_, hdeg, 0, (routingH B e).toAddSubmonoid.zero_mem, by simp⟩
    rw [← colon_piece_exact B e HD hn hd heq hcases] at hg
    obtain ⟨hxH,hn,h,hh,hx⟩ := hg
    exact ⟨hxH,n,hn,h,hh,hx⟩
  · obtain ⟨delta,U,V,hdom,heq,hz⟩ := hprincipal
    let q0 := firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e)
    have hspec := firstPrincipal_spec (routingH B e) (routingM B e) (routingM_pos B e)
    have hprincipal : q0 * routingM B e ∈ cyclicCut (routingH B e) (routingM B e) :=
      ⟨hspec.2,q0,hspec.1,0,(routingH B e).toAddSubmonoid.zero_mem,by simp⟩
    have hr := coherent_normalized_relations B e HD
    have hprincipal_eq : q0 * routingM B e =
        delta * routingA B e + U * routingB B e + V * routingC B e := by
      simpa [q0, normalizedGrid] using heq
    rcases hz with rfl | rfl | rfl
    · simpa [monomialDegree, ← heq] using hprincipal
    · have hI := congrArg (fun z => z * routingB B e)
        (Nat.sub_add_cancel (Nat.le_of_lt hdom.1))
      simp only [Nat.add_mul] at hI
      have hPB : monomialDegree B e (delta+cr21 HD,0,V+cr23 HD) =
          q0 * routingM B e + normalizedGrid B e 0 (c2 B e-U) 0 := by
        simp only [monomialDegree, normalizedGrid, Nat.add_mul, zero_mul, zero_add, add_zero]
        nlinarith only [hprincipal_eq, hr.2.1, hI]
      rw [hPB]
      exact cut_add_H hprincipal (grid_mem_H B e _ _ _)
    · have hJ := congrArg (fun z => z * routingC B e)
        (Nat.sub_add_cancel (Nat.le_of_lt hdom.2.1))
      simp only [Nat.add_mul] at hJ
      have hPC : monomialDegree B e (delta+cr31 HD,U+cr32 HD,0) =
          q0 * routingM B e + normalizedGrid B e 0 0 (c3 B e-V) := by
        simp only [monomialDegree, normalizedGrid, Nat.add_mul, zero_mul, zero_add, add_zero]
        nlinarith only [hprincipal_eq, hr.2.2, hJ]
      rw [hPC]
      exact cut_add_H hprincipal (grid_mem_H B e _ _ _)

/-- The polynomial monomial closure has only genuine H-cut degrees.
The converse on the canonical domain is the next T4 obligation. -/
theorem monomialClosure_degree_mem_cut
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {z : Monomial}
    (hz : z ∈ monomialClosure (canonicalIdealGenerators B e HD)) :
    monomialDegree B e z ∈ cyclicCut (routingH B e) (routingM B e) := by
  obtain ⟨g,hg,hr,hi,hj⟩ := hz
  have hR := congrArg (fun n => n * routingA B e) (Nat.sub_add_cancel hr)
  have hI := congrArg (fun n => n * routingB B e) (Nat.sub_add_cancel hi)
  have hJ := congrArg (fun n => n * routingC B e) (Nat.sub_add_cancel hj)
  simp only [Nat.add_mul] at hR hI hJ
  have heq : monomialDegree B e z = monomialDegree B e g +
      normalizedGrid B e (z.1-g.1) (z.2.1-g.2.1) (z.2.2-g.2.2) := by
    simp only [monomialDegree, normalizedGrid]
    omega
  rw [heq]
  exact cut_add_H (canonicalIdealGenerators_degree_mem_cut B e HD hg)
    (grid_mem_H B e _ _ _)

end NS25Lean.L5A2C4OR20
