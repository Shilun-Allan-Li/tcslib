# S2 native seal driver — preparation and limits

Driver frozen for root review/run:

`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/s2_native_seal_driver.py`

SHA256: `0c58a5d287dd1487dc5bbda47283ad4ab9e3c5fe0ba50e9c902c369df55fa7e8` (39,350 bytes; 615 lines).

No driver command, maintainer builder, Git subprocess, native checker, Lean/cache command, or evidence preparation was run by this invocation. Only the trusted driver and this note were written under the ignored Gate06 repairs directory. The prepared head manifests, probes, library sources, and earlier review artifacts were not edited.

## Commands for root

Run serially, with no concurrent native check using this S2 object tree:

```sh
python3 -I /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/s2_native_seal_driver.py prepare-base
python3 -I /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/s2_native_seal_driver.py run-seals --run-id r1
python3 -I /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/s2_native_seal_driver.py run-controls --run-id r1
```

The driver pins the S2 checkout to `d8c4cfed793f04062e7e79b78344e5b593ff3ddc`. Every generic-check subprocess uses that checkout as its working directory, regardless of the launch directory. It invokes `check_probe_s2.py` with `check=False`, so an expected proof failure (exit 1) remains available for diagnostic validation. The driver itself serializes its checks; it does not lock out another maintainer process.

The main evidence directory is:

`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/fills/shared-lemmas/s2/final/maintainer-rule10`

`prepare-base` creates fresh `base-seals` evidence copies/metadata and `base-seal-manifest.json`. Actual base `.lean` probes are confined to the S2 checkout's `.lake/ps-maintainer/gate06/rule10/base-seals/`. It retains exact original source bytes, their Git blob identity, generated probe bytes, insertions, and line maps. It uses the configured V3 payload and each corresponding head seal's full foreign-name list, without weakening the list for the base.

The current evidence pin selects base `34cc6518dcceb62fcac4f1cf2dcd9c4c37971c94`; this is distinct from the issued S2 source ancestor `31348fcf7dee32f84db1fc8f929d80653137995e`. The driver follows `pins.json`. Base probes import the existing **head** objects; it does not rebuild or claim a base olean environment.

`run-seals` creates a fresh `native-seal-runs/<run-id>/` with sequential head-five then base-five attempts, exact source captures, generic results/logs, classifications, and comparisons. `run-controls` similarly creates `native-control-runs/<run-id>/` for all eleven prepared controls. Existing output directories, files, probes, or manifests are refused rather than overwritten. There is no automatic resume: retain an incomplete attempt and choose a new run ID after resolving its cause.

## Validation performed by the driver

Before and around native attempts it checks frozen HEAD, library bytes/path set, prepared source/closure metadata, all captured evidence/tool inputs, exact regenerated probe bytes and line maps, and the generic checker's pinned hash. Tools are loaded only after matching their pinned hashes; delivered worker programs are not executed. It relies on root's native prerequisite setup; it does not independently rebuild or re-audit imported objects.

Each whole-file run must have the complete, unique actual-name installation rows, exact active/already-irreducible counts, and the exact EOF marker. A valid failure must have exit 1 and located source diagnostics, and every diagnostic must map to an original source line. Errors in seal insertions, missing markers, stale successful objects, unexpected result codes, missing diagnostics, or changed inputs cannot count as a source failure or a pass. Warnings remain captured and counted in result records.

The eleven controls are regenerated from the pinned maintainer model and checked against their exact prepared bytes, targets, reader catalog, proof regions, and expectations. Before/after catalogs and body markers must appear in order. A sealed negative must have exactly its expected sole proof error on its recorded `rfl` line, between body markers. The anonymous and matcher cases receive the same full checks; a harness failure cannot establish sensitivity. All five unsealed negatives and the sealed published-reader control must succeed with fresh nonempty objects.

Every failure is retained and classified. There is no source-failure exemption list. Source-name comparisons are lexical locations in original source (including normalized `_root_.` qualification), not a claim about elaborated declaration identities or equality of proof blocks. Both sides must have valid harnesses before their spelling comparison is marked valid. `raw_block_identity` remains `NOT_CHECKED`, and touched-failure reconciliation remains pending.

With valid harnesses, `run-seals` can exit 0 while reporting source errors: this means the survey completed, not that the sources passed. Its summary remains `COMPLETED_VALID_HARNESSES_SOURCE_REVIEW_PENDING`. Retained harness failures make the command exit 1 after writing its summary. `run-controls` exits 0 only when all eleven expected outcomes are verified; unexpected/harness outcomes are retained and produce exit 1. Early input/setup errors fail closed and may occur before an attempt summary exists.

## Static checks and remaining verification

Python AST parsing passed for the frozen driver. Earlier pure-function checks (without calling `main`, `load_context`, imported builders, or subprocess functions) verified the completed collector's 1,292 standard-only own axiom rows; accepted a synthetic complete installation with active/already-irreducible names; rejected duplicate EOF, wrong counts, and wrong identity; parsed ordinary and coded diagnostics; and checked namespace/root-qualified lexical source locations. The final added expectation/status checks were AST-parsed but not runtime exercised.

No native result is claimed. Root's real `prepare-base`, ten sealed runs, and eleven control runs are the meaningful remaining checks. Raw source-block identity, failure attribution, and landing clearance require subsequent maintainer review. These notes add no approval gate or library requirement.

Pinned native checker SHA256: `3d66d1429cc502f68baf64a4fc9c6cd145fef67578fcba5a92b8725e6342d8d6`.

Pinned preparation tool SHA256 values:

- `build_seals.py`: `fae07000e8c3fda22225632ded45208e2651bab827d827639f48d46e2005347a`
- `build_controls.py`: `484009543d095685b50fea244427adf4907de11bd5ef6a9e17e76fe08c60cf89`
- `request_payload_adapter.py`: `ae79f1ec66e93c8bc7749a53e12e3d383feda020ad2978520a0cfa24b12eb5de`
