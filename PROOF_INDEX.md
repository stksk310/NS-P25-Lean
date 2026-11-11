# Proof index

All public invariants below belong to the original Gamma. Write `t = Gamma.asRelativeIdeal.idealType` and `rho = NS25Lean.Presentation.rho Gamma`; subtraction in these public statements is natural-number subtraction.

| Preserved result | Declaration | Exact scope |
|---|---|---|
| NS-SHARP | `NS25Lean.L4B.ns_sharp` | Embedding dimension four implies `t ≤ rho - 1`. |
| P2-STRONG | `NS25Lean.P2Strong.p2_strong` | Original `M : L2B.MultiplicityBase Gamma`, `chosenDefect M.base = 2`, implies `t ≤ rho - 2`. |
| P3-STRONG | `NS25Lean.P3R68.p3_strong_of_chosenDefect_three` | Original M and defect three imply `t ≤ rho - 2`. |
| Finite intrinsic equality | `NS25Lean.EC.R75.finite_intrinsic_equality_iff` | Original Gamma and M: `t = rho - 1 ↔ FiniteEqualityCertificate M`. |
| All original pivots | `NS25Lean.EC.R75.equality_iff_all_original_pivots` | Original `B : ChosenBase.Data Gamma`: equality iff every `atPivot B i` has its guarded finite certificate. |

The literal applications in [PublicExactTargets.lean](PublicExactTargets.lean), [PublicAxioms.lean](PublicAxioms.lean), and [PublicCertificateAudit.lean](PublicCertificateAudit.lean) remain byte-identical to the preserved baseline. Their final executions are recorded in verification/BUILD_RECEIPT.json. The expected axiom footprint is limited to Lean-standard `propext`, `Classical.choice`, and `Quot.sound`.

## Revised proof routes

| Manuscript change | Current Lean route |
|---|---|
| Whole minimal-source fibers | [PrincipalSourceFibers.lean](NS25Lean/PrincipalSourceFibers.lean) proves source paths, integer differences, complete normalized chains and uniqueness without a shared-coordinate premise. [InactiveBinomialFibers.lean](NS25Lean/InactiveBinomialFibers.lean) derives its inactive-presentation corollary from the actual toric presentation. Existing source/order callers use the shared core. |
| Original-pivot monomial strictness | [MonomialPivotStrictness.lean](NS25Lean/MonomialPivotStrictness.lean) proves full support implies defect at most one for any original datum and field. Two-axis exclusion, actual component extraction and the local contribution bound are proved in its helpers. A/D and P3 R0 now consume this theorem. |
| Return exchange and C compensation | [P2ReturnExchange.lean](NS25Lean/P2ReturnExchange.lean) supplies guarded return/source laws. [AttainedCapCompensation.lean](NS25Lean/AttainedCapCompensation.lean) proves the common rectangle/quadrant inequality. The positive and pure-pair actual adapters feed [P2SectorCSharedClosure.lean](NS25Lean/P2SectorCSharedClosure.lean), used by the terminal five-sector assembly. |
| Principal tensor-colon cut | [PrincipalTensorColon.lean](NS25Lean/PrincipalTensorColon.lean) exports the arbitrary-field coordinate tensor-colon theorem, derived mixed-cycle rank and negative colon-socle balance. [PrincipalTensorColonLiteralType.lean](NS25Lean/PrincipalTensorColonLiteralType.lean) derives actual integral-socle/source cardinality conclusions for the same principal adjoin. The actual nonsymmetric B caller invokes the full theorem; symmetric surgery uses its early shared linear balance. |
| Same final cut and protected corners | [P3CommonFinalCountAlignment.lean](NS25Lean/P3CommonFinalCountAlignment.lean), [P3CriticalDivisorAlignment.lean](NS25Lean/P3CriticalDivisorAlignment.lean), and the R1/R2/R3 alignment modules share cancellation, critical-divisor, all-floor staircase and protected-corner arguments. The actual final nonexceptional image and fake sinks are retained. |
| Common equality losses and permitted tags | [EqualityLossAlgebra.lean](NS25Lean/EqualityLossAlgebra.lean) is consumed by both old loss identities. [ECDirectStaircaseR74.lean](NS25Lean/ECDirectStaircaseR74.lean) treats arbitrary fields and every tag satisfying the actual coordinate specification. Tie equality retains tag surjectivity **and** integer PC, including Q=0. |
| Existential equality without F2/F3 | `NS25Lean.EC.R75.equality_iff_some_original_certificate` in [ECFiniteExistentialR76.lean](NS25Lean/ECFiniteExistentialR76.lean) characterizes equality by an unguarded Mon-or-Tie witness at some original pivot. The witness layer and trichotomy do not import the P2/P3 strong endpoints. The older guarded all-pivot necessity remains a separate route. |

The original arbitrary-pivot strict-bound adapters retain their proved dilation/multiplicity transfer route. No new direct-at-pivot geometric proof is asserted merely from the original conclusion. The monomial strictness theorem's arbitrary-pivot transfer is exact equality of the actual J and chosen defect, not an identification of source counts at unrelated pivots.

The finite equality certificate uses actual original-J monomial saturation or an actual one-tie frontend with normalized sources and PCR counts. Equality itself is not a witness field. The unguarded existential criterion and guarded all-pivot criterion remain distinct; transfer compatibility does not identify nested frontend witnesses.

## Coverage and limits

The [alignment matrix](verification/ALIGNMENT_SCOPE.md) records the exact scope of the 27 families and 246 manuscript operations. The [build receipt](verification/BUILD_RECEIPT.json) binds all 494 current Lean sources to their successful compilation logs. The original three public drivers are unchanged.

The conditional H1P/H1M supplements retain inherited unformalized strong EXHAUST/endpoint statements. Historical geometric NEIT/NEIT* and six-cell PCR remain outside this release's formal claims. No whole-paper certification or journal endorsement is asserted.

## Standalone common chapter APIs

| Scope | Main source and interface |
|---|---|
| Original-pivot Apéry/source intervals | [OriginalSourceFibers.lean](NS25Lean/OriginalSourceFibers.lean): actual original tie and full fiber law from defect one; proved internal dilation route retained |
| Generic floor, sentinel and directional axis cases | [GenericFloorStaircase.lean](NS25Lean/GenericFloorStaircase.lean), [GenericFloorDirectional.lean](NS25Lean/GenericFloorDirectional.lean), [GenericFloorExceptional.lean](NS25Lean/GenericFloorExceptional.lean) |
| True critical tail presentations | [SharedTailPositiveCritical.lean](NS25Lean/SharedTailPositiveCritical.lean), [SharedTailKernel.lean](NS25Lean/SharedTailKernel.lean), [SharedTailPurePairApery.lean](NS25Lean/SharedTailPurePairApery.lean) |
| Physical normalization and all common returns | [GenericPhysicalNormalization.lean](NS25Lean/GenericPhysicalNormalization.lean), [GenericReturnCommonTheorems.lean](NS25Lean/GenericReturnCommonTheorems.lean) |
| Full critical C duality and actual count transport | [P2GenericCriticalDuality.lean](NS25Lean/P2GenericCriticalDuality.lean), [P2ActualGenericDualityCounts.lean](NS25Lean/P2ActualGenericDualityCounts.lean), [P2PurePairGenericDualityCounts.lean](NS25Lean/P2PurePairGenericDualityCounts.lean) |
| Literal tensor-colon socle/source counts | [PrincipalTensorColonLiteralType.lean](NS25Lean/PrincipalTensorColonLiteralType.lean) |

The current [27-family/246-operation matrix](verification/ALIGNMENT_SCOPE.md) distinguishes the new exact statements from inherited H1 endpoint gaps. Kernel/presentation form supplies the tail quotient clause; no separate named quotient AlgEquiv or bundled physical SimpleGraph.Iso constant is advertised.
