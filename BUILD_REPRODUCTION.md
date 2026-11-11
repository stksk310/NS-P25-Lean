# Build reproduction

Install the exact `lean-toolchain`. Preserve `lakefile.toml` and `lake-manifest.json`; do not run `lake update`. `lake exe cache get` may obtain external pinned dependency caches. For a source-clean project replay, begin without project `.lake/build` outputs.

```sh
lake exe cache get
lake build NS25Lean
lake env lean PublicExactTargets.lean
lake env lean PublicAxioms.lean
lake env lean PublicCertificateAudit.lean
```

The production root exports the common manuscript modules. Remaining standalone verification files can be elaborated with `lake env lean PATH.lean`; the complete 494-file list is in `verification/SOURCE_SHA256.json`. Files under `Checks/` and the standalone `Alignment*Accept.lean` files are successful positive/boundary controls, not expected failures. Likewise, the check modules within `NS25Lean/` are included in the 494-file receipt. To check all listed sources after the production build, for example:

```python
import json, subprocess
from pathlib import Path
sources = json.loads(Path('verification/SOURCE_SHA256.json').read_text())
for source in sources:
    subprocess.run(['lake', 'env', 'lean', source], check=True)
```

The 13 original individual controls are in `legacy-checks/`: five `axioms/` files must succeed with only standard axioms, and eight `negative/` files must fail with an actual type mismatch, not a missing import. Their updated-source executions are in `verification/LEGACY_CHECKS.json`.

## Evidence supplied with v1.1.0

The alignment task compiled the full baseline of 395 files from source, then built an intermediate checkpoint and the final 494-file source set. The final pass compiled 42 and reused 452 exact task-fresh outputs, checking source, dependency-object, compiler and output hashes. Its LEAN_PATH excluded inherited project objects. External dependencies were warm and pinned. All final exit codes were zero. `verification/BUILD_RECEIPT.json` publishes the source/log bindings; its logs are copied verbatim from that completed run. Public metadata edits do not change the 494 checked sources.

No new independent-host or dependency-cold replay of v1.1.0 is claimed. The old v1.0.0 Ubuntu replay is historical evidence for that release only. Reproduction commands above are instructions, not claims that those commands were executed for this publication packaging step.
