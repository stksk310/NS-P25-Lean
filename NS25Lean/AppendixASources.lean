import NS25Lean.OneDefectFrontend

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- Removing any used variable from an actual minimal source lands in Apéry. -/
theorem source_remove_apery (F : InternalFrontend k M h) (s : Source M.base)
    (u : FactorizationFiber M.base s.val) (j : Fin 3) (hj : 0 < u.val j) :
    s.val - weights M.base j ∈ M.base.apery := by
  have he := removed_weight M.base s.val u j hj
  have hw := weights_positive M.base j
  rw [M.base.apery_eq_compl]
  refine ⟨?_, ?_⟩
  · have hm := (Presentation.factorizationMap M.base.tailDegrees
      (u.val - Finsupp.single j 1)).property
    rw [← weight_eq_degree] at hm
    convert hm using 1 <;> omega
  · rcases s.property.2 (weights M.base j) (M.base.tailDegrees j).property hw.ne' with ht | ht
    · omega
    · exact ht

/-- Natural-number form of the actual Apéry decomposition; no source restriction is assumed. -/
theorem apery_decomposition (B : Data Gamma) (w : ℕ) (hw : w ∈ Gamma) :
    ∃ ω ∈ B.apery, ∃ d : ℕ, w = ω + d * B.q.val := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    by_cases ha : w ∈ B.apery
    · exact ⟨w, ha, 0, by simp⟩
    · have hn : B.q.val ≤ w ∧ w - B.q.val ∈ Gamma := by
        change ¬ (w ∈ Gamma.toAddSubmonoid ∧ (w < B.q.val ∨ w - B.q.val ∉ Gamma.toAddSubmonoid)) at ha
        constructor
        · by_contra ht; exact ha ⟨hw, Or.inl (by omega)⟩
        · by_contra ht; exact ha ⟨hw, Or.inr ht⟩
      obtain ⟨ω, hω, d, hd⟩ := ih (w - B.q.val) (by have := B.q_positive; omega) hn.2
      refine ⟨ω, hω, d + 1, ?_⟩
      rw [Nat.add_mul, one_mul]
      omega

theorem source_apery_decomposition (F : InternalFrontend k M h) (s : Source M.base) :
    ∃ ω ∈ M.base.apery, ∃ d : ℕ, 1 ≤ d ∧ s.val = ω + d * M.base.q.val := by
  obtain ⟨ω, hω, d, hd⟩ := apery_decomposition M.base s.val (M.base.H_le s.property.1.1)
  refine ⟨ω, hω, d, ?_, hd⟩
  by_contra hn
  have he : s.val = ω := by
    have hz : d = 0 := by omega
    simpa [hz] using hd
  have ha := (M.base.apery_eq_compl ▸ hω).2
  exact ha (he ▸ s.property.1)

/-- SUP-COMP, for every pair of actual source and residual factorizations. -/
theorem source_apery_support_complement (F : InternalFrontend k M h) (s : Source M.base)
    (ω d : ℕ) (hd : 1 ≤ d) (he : s.val = ω + d * M.base.q.val)
    (u : FactorizationFiber M.base s.val) (v : FactorizationFiber M.base ω)
    (j : Fin 3) (hu : 0 < u.val j) : v.val j = 0 := by
  by_contra hv
  have hvpos : 0 < v.val j := Nat.pos_of_ne_zero hv
  have hs := source_remove_apery F s u j hu
  have hnot := (M.base.apery_eq_compl ▸ hs).2
  have huweight := removed_weight M.base s.val u j hu
  have hvweight := removed_weight M.base ω v j hvpos
  have hm : ω - weights M.base j ∈ Gamma.toAddSubmonoid := by
    apply M.base.H_le
    have ht := (Presentation.factorizationMap M.base.tailDegrees
      (v.val - Finsupp.single j 1)).property
    rw [← weight_eq_degree] at ht
    convert ht using 1 <;> omega
  have hp : d * M.base.q.val = (d - 1) * M.base.q.val + M.base.q.val := by
    conv_lhs => rw [← Nat.sub_add_cancel hd]
    rw [Nat.add_mul, one_mul]
  have hadd : (ω - weights M.base j) + (d - 1) * M.base.q.val ∈ Gamma.toAddSubmonoid := by
    simpa [nsmul_eq_mul] using Gamma.toAddSubmonoid.add_mem hm
      (Gamma.toAddSubmonoid.nsmul_mem M.base.q.property (d - 1))
  apply hnot
  refine ⟨(M.base.apery_eq_compl ▸ hs).1, ?_, ?_⟩
  · omega
  · convert hadd using 1 <;> omega

/-- A full-support source has residue-zero Apéry representative. -/
theorem full_support_source_residue_zero (F : InternalFrontend k M h) (s : Source M.base)
    (u : FactorizationFiber M.base s.val) (hu : ∀ j, 0 < u.val j) :
    ∃ d : ℕ, 1 ≤ d ∧ s.val = d * M.base.q.val := by
  obtain ⟨ω, hω, d, hd, he⟩ := source_apery_decomposition F s
  obtain ⟨v⟩ := fiber_nonempty M.base ⟨ω, (M.base.apery_eq_compl ▸ hω).1⟩
  have hv : v.val = 0 := by
    ext j
    exact source_apery_support_complement F s ω d hd he u v j (hu j)
  have hzero : ω = 0 := by simpa [hv] using v.property.symm
  exact ⟨d, hd, by simpa [hzero] using he⟩

/-- An Apéry element cannot be a positive multiple-of-pivot shift of another member. -/
theorem apery_shift_eq (B : Data Gamma) {u v d : ℕ} (hu : u ∈ B.apery)
    (hv : v ∈ B.apery) (he : v = u + d * B.q.val) : u = v := by
  by_cases hd : d = 0
  · simpa [hd] using he.symm
  have hp : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  have hm : u + (d - 1) * B.q.val ∈ Gamma.toAddSubmonoid := by
    simpa [nsmul_eq_mul] using Gamma.toAddSubmonoid.add_mem hu.1
      (Gamma.toAddSubmonoid.nsmul_mem B.q.property (d - 1))
  have hdq : d * B.q.val = (d - 1) * B.q.val + B.q.val := by
    conv_lhs => rw [← Nat.sub_add_cancel hp]
    rw [Nat.add_mul, one_mul]
  rcases hv.2 with ht | ht
  · omega
  · exfalso
    apply ht
    convert hm using 1 <;> omega

/-- Residue-zero firewall for distinct source degrees sharing an actual variable. -/
theorem residue_zero_source_firewall (F : InternalFrontend k M h)
    (s t : Source M.base) (d e : ℕ) (hs : s.val = d * M.base.q.val)
    (ht : t.val = e * M.base.q.val) (u : FactorizationFiber M.base s.val)
    (v : FactorizationFiber M.base t.val) (j : Fin 3) (hu : 0 < u.val j)
    (hv : 0 < v.val j) : s = t := by
  have ha := source_remove_apery F s u j hu
  have hb := source_remove_apery F t v j hv
  have huw := removed_weight M.base s.val u j hu
  have hvw := removed_weight M.base t.val v j hv
  have heq : s.val - weights M.base j = t.val - weights M.base j := by
    rcases le_total d e with hde | hed
    · apply apery_shift_eq M.base (d := e - d) ha hb
      have hm : e * M.base.q.val = d * M.base.q.val + (e - d) * M.base.q.val := by
        rw [← Nat.add_mul, Nat.add_sub_of_le hde]
      omega
    · symm
      apply apery_shift_eq M.base (d := d - e) hb ha
      have hm : d * M.base.q.val = e * M.base.q.val + (d - e) * M.base.q.val := by
        rw [← Nat.add_mul, Nat.add_sub_of_le hed]
      omega
  apply Subtype.ext
  omega

end NS25Lean.L3C
