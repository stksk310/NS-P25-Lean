import NS25Lean.SharedTailConsequences
import NS25Lean.SharedTailPurePairGraph

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTailChecks
open SharedTail CriticalCapGeometry CriticalPresentationModes

example {H : NumericalSemigroup} {B : Base H} (D : Mode B) (k : Type*) [Field k] :
    Presentation.relationIdeal k D.relations=
      Presentation.relationIdeal k {lr : Exponent×Exponent |
        B.triple.weight lr.1=B.triple.weight lr.2} := mode_exact_ideal D k

example {H : NumericalSemigroup} (D : Positive H) (k : Type*) [Field k] :
    Presentation.relationIdeal k (D.toMode 1 (by decide)).relations=
      RingHom.ker (Presentation.factorizationAlgebraMap k (tailDegrees D.triple)).toRingHom :=
  D.exact_kernel k

example {H : NumericalSemigroup} (D : PurePair H) (R : D.Reduced) (k : Type*) [Field k] :
    Presentation.relationIdeal k R.relations=
      RingHom.ker (Presentation.factorizationAlgebraMap k (tailDegrees D.triple)).toRingHom :=
  R.exact_kernel k

example {H : NumericalSemigroup} (D : Positive H) (x y z : ℤ)
    (he : x*D.a+y*D.b+z*D.c=0) :
    ∃ l k : ℤ, x=-(D.A:ℤ)*l-(D.w:ℤ)*k ∧
      y=(D.p:ℤ)*l-(D.z:ℤ)*k ∧ z=(D.q:ℤ)*l+(D.C:ℤ)*k :=
  D.integer_kernel_basis x y z he

end NS25Lean.SharedTailChecks

#print axioms NS25Lean.SharedTail.mode_connected
#print axioms NS25Lean.SharedTail.mode_exact_ideal
#print axioms NS25Lean.SharedTail.Positive.coefficient_sums
#print axioms NS25Lean.SharedTail.Positive.critical_exact_fiber
#print axioms NS25Lean.SharedTail.Positive.residue_bijective
#print axioms NS25Lean.SharedTail.Positive.apery_chart_iff
#print axioms NS25Lean.SharedTail.Positive.integer_kernel_basis
#print axioms NS25Lean.SharedTail.Positive.exact_kernel
#print axioms NS25Lean.SharedTail.Positive.nonunique_critical_divisor
#print axioms NS25Lean.SharedTail.singleton_component_is_critical
#print axioms NS25Lean.SharedTail.PurePair.third_mem_twoGenerator
#print axioms NS25Lean.SharedTail.PurePair.third_exponent
#print axioms NS25Lean.SharedTail.PurePair.positive_witness_reduction
#print axioms NS25Lean.SharedTail.PurePair.Reduced.exact_kernel
#print axioms NS25Lean.SharedTail.PurePair.integer_symmetry
#print axioms NS25Lean.SharedTail.PurePair.Reduced.apery_rectangle_iff
