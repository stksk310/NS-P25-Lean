import NS25Lean.PrincipalSourceFibers
import NS25Lean.InactiveBinomialFibers

set_option autoImplicit false
noncomputable section
open NS25Lean NS25Lean.ChosenBase NS25Lean.L2B NS25Lean.L2B2A2 NS25Lean.L3B NS25Lean.L3C

example {Gamma : NumericalSemigroup} {k : Type*} [Field k]
    {M : MultiplicityBase Gamma} {h : ℕ} (F : InternalFrontend k M h)
    (s : Source M.base) (u v : FactorizationFiber M.base s.val) :
    ∃ j : ℤ, ∀ i, (v.val i : ℤ) = (u.val i : ℤ) + j * tieDelta F.normal i :=
  source_factorization_difference F s u v

#print axioms NS25Lean.L3C.source_factorization_difference
#print axioms NS25Lean.L3C.source_binomial_mem_principal
#print axioms NS25Lean.L3C.source_factorization_chain
#print axioms NS25Lean.L3C.source_normalized_factorization_chain
#print axioms NS25Lean.L3C.inactive_presentation_paths
#print axioms NS25Lean.L3C.inactive_unique_normal_form
#print axioms NS25Lean.L3C.inactive_factorization_chain
