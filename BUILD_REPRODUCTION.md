# Build reproduction — public source v1.0.0

Proof modules, frozen Lean verification drivers, and pinned Lean configuration bytes are unchanged from the R80 independently reproduced release candidate. The first public GitHub release is tagged v1.0.0; frozen Lake package metadata remains version 0.1.0. No dependency update is authorized.

## Accepted independent execution

R80 used a newly created Ubuntu cloud VM distinct from the prior Windows worker. The unchanged 391 proof modules and four-import NS25Lean root were built with Lean 4.34.0-rc1 (commit 3447a668783dbce1a8fdb97101dd067687b2b418) and Lake 5.0.0-src+3447a66. All nine Git revisions matched lake-manifest.json. The external worker cloned pinned dependencies and obtained the official Mathlib dependency object cache. The project build directory was absent before compilation and no old NS25Lean objects were imported. The build completed 2517 Lake jobs and passed the three positive drivers, five individual standard-only axiom audits and eight type-mismatch negative controls.

Commander accepted the source-bound external run with exact scope on 2026-10-19 after independently checking source integrity and provider execution evidence. This was an audit of the worker's actual Linux Lean execution; Commander did not locally perform another kernel build. R81's optional local staging checks are separately recorded in the private audit and do not constitute another independent-host acceptance.

## Fresh kernel replay

1. Copy only the source candidate into a new working directory. Do not copy .lake, OLEAN/ILEAN, compiled caches or old project outputs.
2. Install the exact lean-toolchain. Preserve lakefile.toml and lake-manifest.json byte-for-byte; do not run lake update.
3. Obtain the nine pinned dependencies. lake exe cache get may obtain the Mathlib dependency cache. Record the cache source and confirm the project .lake/build is absent before lake build.
4. Run lake build NS25Lean. Then run lake env lean PublicExactTargets.lean, PublicAxioms.lean and PublicCertificateAudit.lean separately. Preserve full output and exit codes.
5. Run each of the five checks/axioms/*.lean files using lake env lean. Require exit 0 and only propext, Classical.choice and Quot.sound for the exact intended theorem.
6. Run each of the eight checks/negative/*.lean files separately. Require a nonzero exit caused by Type mismatch; unknown modules, unknown identifiers or failed loads do not count as a successful negative control.
7. Confirm the 391 module files plus root are generated, inspect the certificate definitions and final theorem prints, and compare all protected source and dependency-file hashes before and after.

## Historical regression boundary

R78 ran the original 182 research regression drivers against the full frozen research project. That frozen receipt is inherited in R81; the 182 regressions are not rerun here. The curated public source tree does not contain the entire historical research root or suite. Do not run those tests against a different root and label that as the original regression replay. R81's 13 individual checks are five axiom drivers plus eight expected-negative drivers, not the 182-regression suite.

Source validators and saved-receipt validators do not invoke Lean. Their PASS results do not substitute for a kernel execution. The R80 accepted external build remains the independent-host authority. The author selected Apache-2.0, confirmed attribution to Keisuke Sato, and authorized publication through GitHub and Zenodo on 2026-10-23. These are documentation-only changes; R80 remains the accepted distinct-host kernel reproduction for the frozen Lean source. The actual GitHub release and Zenodo DOI must be verified from live services, not inferred from this file.
