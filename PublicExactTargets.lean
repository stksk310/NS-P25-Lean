import NS25Lean.BasePivotSharp
import NS25Lean.P2StrongOriginalR50
import NS25Lean.P3StrongAssemblyR68
import NS25Lean.ECFiniteAllPivotsR75

set_option autoImplicit false
noncomputable section

example (Gamma : NS25Lean.NumericalSemigroup)
    (he : NS25Lean.CoarseP25.HasEmbeddingDimensionFour Gamma) :
    Gamma.asRelativeIdeal.idealType ≤ NS25Lean.Presentation.rho Gamma - 1 :=
  NS25Lean.L4B.ns_sharp Gamma he

example {Gamma : NS25Lean.NumericalSemigroup}
    (M : NS25Lean.L2B.MultiplicityBase Gamma)
    (hp : NS25Lean.L2B.chosenDefect M.base = 2) :
    Gamma.asRelativeIdeal.idealType ≤ NS25Lean.Presentation.rho Gamma - 2 :=
  NS25Lean.P2Strong.p2_strong M hp

example {Gamma : NS25Lean.NumericalSemigroup}
    (M : NS25Lean.L2B.MultiplicityBase Gamma)
    (hp : NS25Lean.L2B.chosenDefect M.base = 3) :
    Gamma.asRelativeIdeal.idealType ≤ NS25Lean.Presentation.rho Gamma - 2 :=
  NS25Lean.P3R68.p3_strong_of_chosenDefect_three M hp

example (Gamma : NS25Lean.NumericalSemigroup)
    (M : NS25Lean.L2B.MultiplicityBase Gamma) :
    Gamma.asRelativeIdeal.idealType = NS25Lean.Presentation.rho Gamma - 1 ↔
      NS25Lean.EC.R75.FiniteEqualityCertificate M :=
  NS25Lean.EC.R75.finite_intrinsic_equality_iff Gamma M

example {Gamma : NS25Lean.NumericalSemigroup}
    (B : NS25Lean.ChosenBase.Data Gamma) :
    Gamma.asRelativeIdeal.idealType = NS25Lean.Presentation.rho Gamma - 1 ↔
      ∀ i : Fin 4, NS25Lean.EC.R75.PivotFiniteCertificate
        (NS25Lean.L2C.atPivot B i) :=
  NS25Lean.EC.R75.equality_iff_all_original_pivots B

#print axioms NS25Lean.L4B.ns_sharp
#print axioms NS25Lean.P2Strong.p2_strong
#print axioms NS25Lean.P3R68.p3_strong_of_chosenDefect_three
#print axioms NS25Lean.EC.R75.finite_intrinsic_equality_iff
#print axioms NS25Lean.EC.R75.equality_iff_all_original_pivots
