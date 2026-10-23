import NS25Lean.AppendixASourceOrder

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

theorem source_factorization_nonzero (B : Data Gamma) (s : Source B)
    (u : FactorizationFiber B s.val) : ∃ j, 0 < u.val j := by
  by_contra hn
  have hu : u.val = 0 := by ext j; simp only [Finsupp.zero_apply]; by_contra hj; exact hn ⟨j, Nat.pos_of_ne_zero hj⟩
  have hs : s.val = 0 := by simpa [hu] using u.property.symm
  have hq := s.property.1.2.1
  have hp := B.q_positive
  omega

theorem unique_residue_zero_source (F : InternalFrontend k M h)
    (s t : Source M.base) (d e : ℕ) (hs : s.val = d * M.base.q.val)
    (ht : t.val = e * M.base.q.val) (u : FactorizationFiber M.base s.val)
    (hu : ∀ j, 0 < u.val j) : s = t := by
  obtain ⟨v⟩ := fiber_nonempty M.base ⟨t.val, t.property.1.1⟩
  obtain ⟨j, hj⟩ := source_factorization_nonzero M.base t v
  exact residue_zero_source_firewall F s t d e hs ht u v j (hu j) hj

theorem shared_slab_source_unique (F : InternalFrontend k M h)
    (s : Source M.base) (u v : FactorizationFiber M.base s.val) (j : Fin 3)
    (hu : 0 < u.val j) (hv : 0 < v.val j)
    (huSlab : u.val (F.normal.perm 0) < F.normal.a)
    (hvSlab : v.val (F.normal.perm 0) < F.normal.a) : u = v := by
  obtain ⟨z, hz⟩ := shared_source_factorization_difference F s u v j hu hv
  have hx := hz (F.normal.perm 0)
  rw [tieDelta_x] at hx
  have ha := F.normal.a_ge_two
  have hz0 : z = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · have hz1 : z ≤ -1 := by omega
      have hm : z * (F.normal.a : ℤ) ≤ -1 * (F.normal.a : ℤ) :=
        mul_le_mul_of_nonneg_right hz1 (by positivity)
      omega
    · have hz1 : 1 ≤ z := by omega
      have hm : 1 * (F.normal.a : ℤ) ≤ z * (F.normal.a : ℤ) :=
        mul_le_mul_of_nonneg_right hz1 (by positivity)
      omega
  apply Subtype.ext
  ext i
  have hi := hz i
  simp only [hz0, zero_mul, add_zero] at hi
  exact_mod_cast hi.symm

/-- Actual full-support depth dominance, derived from source minimality. -/
theorem full_support_depth_dominance (F : InternalFrontend k M h)
    (s t : Source M.base) (ω d e : ℕ) (hω : ω ∈ M.base.apery) (hωpos : ω ≠ 0)
    (hs : s.val = ω + d * M.base.q.val) (ht : t.val = e * M.base.q.val)
    (v : FactorizationFiber M.base t.val) (hv : ∀ j, 0 < v.val j) : d < e := by
  by_contra hn
  have hed : e ≤ d := by omega
  by_cases heq : d = e
  · subst d
    exact source_no_positive_translate M.base t s ω
      (M.base.apery_eq_compl ▸ hω).1 (Nat.pos_of_ne_zero hωpos) (by omega)
  obtain ⟨u⟩ := fiber_nonempty M.base ⟨s.val, s.property.1.1⟩
  obtain ⟨j, hj⟩ := source_factorization_nonzero M.base s u
  have hsa := source_remove_apery F s u j hj
  have hta := source_remove_apery F t v j (hv j)
  have huweight := removed_weight M.base s.val u j hj
  have hvweight := removed_weight M.base t.val v j (hv j)
  have hd : e + (d - e - 1) + 1 = d := by omega
  have hdq := congrArg (fun n => n * M.base.q.val) hd
  simp only [Nat.add_mul, one_mul] at hdq
  have hm : ω + (d - e - 1) * M.base.q.val + (t.val - weights M.base j) ∈ Gamma.toAddSubmonoid := by
    apply Gamma.toAddSubmonoid.add_mem
    · exact Gamma.toAddSubmonoid.add_mem hω.1 (by
        simpa [nsmul_eq_mul] using Gamma.toAddSubmonoid.nsmul_mem M.base.q.property (d - e - 1))
    · exact hta.1
  have hk : s.val - weights M.base j ∈ M.base.K := by
    refine ⟨(M.base.apery_eq_compl ▸ hsa).1, ?_, ?_⟩
    · omega
    · convert hm using 1 <;> omega
  exact (M.base.apery_eq_compl ▸ hsa).2 hk

end NS25Lean.L3C
