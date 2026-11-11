import NS25Lean.SharedTailPositiveNormalForm
import NS25Lean.SharedTailPurePairNormal

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse L3C

def tailDegrees {H : NumericalSemigroup} (T : Triple H) (i : Fin 3) : H.toAddSubmonoid :=
  ⟨T.g i,T.member (Finsupp.single i 1)⟩

theorem tail_factorization_degree {H : NumericalSemigroup} (T : Triple H) (e : Exponent) :
    (Presentation.factorizationMap (tailDegrees T) e).val=T.weight e := by
  have hh : H.toAddSubmonoid.subtype.comp (Presentation.factorizationMap (tailDegrees T))=T.weight := by
    apply Finsupp.addHom_ext
    intro i n
    simp [tailDegrees,Presentation.factorizationMap_single,T.weight_single,nsmul_eq_mul]
  exact DFunLike.congr_fun hh e

/-- The all-equal-weight binomial ideal is the actual map kernel into k[H]. -/
theorem tail_relationIdeal_eq_kernel {H : NumericalSemigroup} (T : Triple H)
    (k : Type*) [Field k] :
    Presentation.relationIdeal k {lr : Exponent×Exponent | T.weight lr.1=T.weight lr.2}=
      RingHom.ker (Presentation.factorizationAlgebraMap k (tailDegrees T)).toRingHom := by
  rw [←Presentation.relationIdeal_factorization_eq_ker]
  congr 1
  ext lr
  change T.weight lr.1=T.weight lr.2 ↔
    Presentation.factorizationMap (tailDegrees T) lr.1=Presentation.factorizationMap (tailDegrees T) lr.2
  rw [←Subtype.val_inj,tail_factorization_degree,tail_factorization_degree]

theorem Positive.exact_kernel {H : NumericalSemigroup} (D : Positive H)
    (k : Type*) [Field k] :
    Presentation.relationIdeal k (D.toMode 1 (by decide)).relations=
      RingHom.ker (Presentation.factorizationAlgebraMap k (tailDegrees D.triple)).toRingHom :=
  (D.exact_ideal k).trans (tail_relationIdeal_eq_kernel D.triple k)

theorem PurePair.Reduced.exact_kernel {H : NumericalSemigroup} {D : PurePair H}
    (R : D.Reduced) (k : Type*) [Field k] :
    Presentation.relationIdeal k R.relations=
      RingHom.ker (Presentation.factorizationAlgebraMap k (tailDegrees D.triple)).toRingHom :=
  (R.exact_ideal k).trans (tail_relationIdeal_eq_kernel D.triple k)

end NS25Lean.SharedTail
