import NS25Lean.GenericReturnActualAdapters

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericReturnChecks
open GenericPhysical GenericReturn SharedTail L5A2C4OR19

example {H Gamma : NumericalSemigroup} (D : Presentation H Gamma)
    (hdelta : D.delta=1) (x : ℕ) :
    x∈D.normalizedCut ↔ x∈H ∧ D.m≤x ∧ x-D.m∈Gamma := by
  simp only [Presentation.normalizedCut,Set.mem_setOf_eq,hdelta,one_mul]

example (H : NumericalSemigroup) (m : ℕ) (hm : 0<m) (hmem : m∈H) :
    firstPrincipal H m hm=1 := (firstPrincipal_eq_one_iff H m hm).mpr hmem

example {H : NumericalSemigroup} (D : Positive H) (nu i j d : ℕ)
    (hr : RB D i j d) (he : (i : ℤ)*D.b+j*D.c=(nu : ℤ)+d*D.a) :
    unionHeight D (fun _ : Unit => nu) (D.z-1) 0=D.A-d := by
  have hh := rb_prefix_gate_heights D (fun _ : Unit => nu) (fun _ => i) (fun _ => j)
    (fun _ => d) (fun _ => hr) (fun _ => he)
  simpa [depthMaximum] using hh.1

#check Presentation.coprime
#check Presentation.normalizedCut_iff_returns
#check Presentation.cut_finite_reduction
#check Presentation.cut_finite_complement
#check Presentation.source_scaling
#check Presentation.socle_scaling
#check Presentation.factorization_graph
#check Presentation.physical_return_multiplier
#check cut_apery_eq_finite_minimum
#check cut_apery_eq_alpha_add_height
#check physical_cutIdeal_eq
#check strict_canonical_return
#check all_live_critical_predecessors_absent
#check StrictFamily.level_one_anchor
#check StrictFamily.common_arm_of_no_full_support
#check prefix_empty_at_one
#check StrictFamily.no_two_arms_at_two
#check Return.exact_generators
#check Return.subset_of_generators_mem
#check canonical_F_representative
#check rb_axis_canonical
#check lt_axis_canonical
#check rb_X_not_ST_target
#check rb_Y_not_ST_target
#check lt_X_not_ST_target
#check lt_Y_not_ST_target
#check rb_prefix_gate_heights
#check lt_prefix_gate_heights
#check actual_return_exact_generators

#print axioms Presentation.coprime
#print axioms Presentation.normalizedCut_iff_returns
#print axioms Presentation.cut_finite_complement
#print axioms Presentation.factorization_graph
#print axioms cut_apery_eq_finite_minimum
#print axioms cut_apery_eq_alpha_add_height
#print axioms strict_canonical_return
#print axioms all_live_critical_predecessors_absent
#print axioms StrictFamily.level_one_anchor
#print axioms StrictFamily.common_arm_of_no_full_support
#print axioms Return.exact_generators
#print axioms rb_axis_canonical
#print axioms lt_axis_canonical
#print axioms rb_X_not_ST_target
#print axioms rb_Y_not_ST_target
#print axioms lt_X_not_ST_target
#print axioms lt_Y_not_ST_target
#print axioms rb_prefix_gate_heights
#print axioms lt_prefix_gate_heights
#print axioms actual_return_exact_generators

end NS25Lean.GenericReturnChecks
