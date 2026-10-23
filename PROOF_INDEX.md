# Proof index

All invariants below are those of the original Gamma. Let `t = Gamma.asRelativeIdeal.idealType` and `rho = NS25Lean.Presentation.rho Gamma` (natural-number subtraction as in Lean).

| Result | Exact declaration | Hypotheses and conclusion | Source |
|---|---|---|---|
| NS-SHARP | `NS25Lean.L4B.ns_sharp` | Original Gamma; `CoarseP25.HasEmbeddingDimensionFour Gamma` implies `t ≤ rho - 1` | [BasePivotSharp.lean](NS25Lean/BasePivotSharp.lean) |
| Original P2-STRONG | `NS25Lean.P2Strong.p2_strong` | Original `M : L2B.MultiplicityBase Gamma`; `L2B.chosenDefect M.base = 2` implies `t ≤ rho - 2` | [P2StrongOriginalR50.lean](NS25Lean/P2StrongOriginalR50.lean) |
| Original P3-STRONG | `NS25Lean.P3R68.p3_strong_of_chosenDefect_three` | Same original M; `chosenDefect M.base = 3` implies `t ≤ rho - 2` | [P3StrongAssemblyR68.lean](NS25Lean/P3StrongAssemblyR68.lean) |
| Finite intrinsic equality | `NS25Lean.EC.R75.finite_intrinsic_equality_iff` | Every original Gamma and M, with no extra premise: `t = rho - 1 ↔ FiniteEqualityCertificate M` | [ECFiniteIntrinsicR75.lean](NS25Lean/ECFiniteIntrinsicR75.lean) |
| Finite ALL-PIVOTS | `NS25Lean.EC.R75.equality_iff_all_original_pivots` | Original `B : ChosenBase.Data Gamma`: `t = rho - 1 ↔ ∀ i : Fin 4, PivotFiniteCertificate (L2C.atPivot B i)` | [ECFiniteAllPivotsR75.lean](NS25Lean/ECFiniteAllPivotsR75.lean) |

[PublicExactTargets.lean](PublicExactTargets.lean) contains the literal typed applications, copied byte for byte from the R78 input. [PublicAxioms.lean](PublicAxioms.lean) prints the axiom footprint of each theorem. Only Lean-standard `propext`, `Classical.choice` and `Quot.sound` are permitted by this release check.

NS-SHARP uses the actual monomial / one-defect / complete-intersection pivot trichotomy. P2 forwards the existing five-sector proof on the same M. P3 splits the actual internal count into 0, 1, 2, 3 and applies the accepted R0–R3 lanes. R75 assembles original-J monomial saturation or actual one-tie frontend/PCR counts; transfer is used internally with explicitly proved invariance, while the final Gamma and M remain original.

The finite certificate is defect 0 with an original-J monomial certificate, or defect 1 with a monomial or one-tie certificate. The monomial certificate requires actual ideal monomiality, q_fs=1 and actual staircase-tag surjectivity. The one-tie certificate uses genuine InternalFrontend and NormalizedSources objects, actual tag surjectivity and the finite PCRCountCertificate. It does not force q_fs=1. Neither the type equality nor an alias to it occurs as a certificate field. PublicCertificateAudit prints these definitions and the supporting structures.

This is a finite formulation, not a formalization of the September NEIT/NEIT*/six-PCR geometric classification. The latter remains open. R80 rebuilt these exact sources on a distinct Ubuntu VM and checked all five exact interfaces, five individual standard-only axiom audits and eight genuine type-mismatch controls. Commander accepted that external execution with exact scope on 2026-10-19; this does not imply a second Commander-local kernel run. Apache-2.0 copyright attribution is now confirmed as **Copyright 2026 Keisuke Sato** in NOTICE. The author authorized GitHub and Zenodo publication of the scoped source corpus on 2026-10-23. This documentation-only release does not change any theorem or kernel execution evidence.
