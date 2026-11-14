# dl-crh evidence tools

These tools prepare and check evidence; their presence does not establish a
completed proof or a passed seal. No tool should be run outside the issued
single-module checking discipline. The root worker owns all Lean invocations.

Use `python3 -I` for every Python command. Do not invoke Lake in the baseline.
The runner calls `scripts/lean_check_tree.sh` once per module, serially, through
the existing shared-host slot gate and timed Lean wrapper.

## Exact baseline

Preparation already staged **98 exact base modules including both original
owners**, at `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`, under
`evidence/probes/Rule10/BaseTree/`. That delivered tree is source-only.

```sh
python3 -I evidence/tools/rule10_run.py base-bootstrap --edition checkpoint1
python3 -I evidence/tools/rule10_run.py base-collect --edition checkpoint1
```

The runner materializes those own source/script bytes under
`.lake/dl-crh-base-work/` and writes independent TCSlib objects under
`.lake/dl-crh-base-oleans/`. The runtime source tree symlinks **this checkout's
own pinned package cache**; no package/build tree is copied and no final-tree
TCSlib olean is added to its Lean path. It preserves original TCSlib module
identities and imports the original base Candidates module, without the two
new readers. Baseline source hashes are checked before each phase. The
collector phase refuses absent, stale or unsuccessful baseline prerequisites.

Every numbered raw module log and `results.jsonl` records source-before/after
hashes, start/end, exit status, log/object hashes and native memory figures.
Do not move active logs. If a bootstrap fails, inspect it and skip dependent
phases. Resource failures remain subject to the environment addendum.

## Final snapshot and collectors

Finish and check every changed/new source module first. Then choose a fresh
edition name (for example `final1`); do not reuse an initialized edition.

```sh
python3 -I evidence/tools/rule10_prepare.py init --edition final1
python3 -I evidence/tools/rule10_run.py final-collect --edition final1
```

The initializer discovers all helper `.lean` files, captures the complete final
TCSlib source closure, emits its source bindings, and generates both the
full-closure collector and all-stored-constant census. The runner requires
current successful check records and matching current oleans for every owner.
It runs `CollectFinal` and `evidence/probes/CensusFinal` through the same module
checker. The census prints `dlHash_crh`'s axioms separately and all stored
constants (including generated/private ones) of every owner.

`checkpoint1` is a preparation snapshot of the partial proof. It must not be
used to certify a later changed final source. The exact baseline is independent
of editions and need not be bootstrapped again after a successful unchanged run.

## Whole-file seals

Use the exact collector log from each successful collector run. Typical paths
are shown; if the attempt number differs, use that actual path.

```sh
python3 -I evidence/tools/rule10_prepare.py seals --edition final1 --side base --collector-log evidence/logs/rule10/checkpoint1/base-collect/evidence_probes_Rule10_CollectBase.001.log
python3 -I evidence/tools/rule10_prepare.py seals --edition final1 --side final --collector-log evidence/logs/rule10/final1/final-collect/evidence_probes_Rule10_final1_CollectFinal.001.log
python3 -I evidence/tools/rule10_run.py seals --edition final1 --side base
python3 -I evidence/tools/rule10_run.py seals --edition final1 --side final
```

Variant A excludes the exact `Complexity.PolyExpr.eval` notation constant;
variant B seals it. Both cover **every ordinary TCSlib definition in the full
transitive import closure**, including generated matchers and definition
instances. Abbreviations/status-reducible nonmatchers are recorded as explicit
exclusions. The generation verifies the compiled import closure against an
independently traversed source closure and verifies stored term references are
covered or explicitly excluded.

The reviewed instrumenter uses actual `Lean.Name` identities and their component
metadata, ordinary local irreducibility attributes and a scoped
instance-unfolding mask that preserves typeclass lookup state. It never enables
unsafe reducibility. Installation and EOF checks are validated for every
128-row chunk. Original source bytes are preserved by insertion-only
instrumentation with source/probe line maps.

Source failures are retained (not treated as harness passes); harness failures
stop the phase and cannot become proof findings. Base/final comparison must
report every failing source declaration or anonymous command. New helper files
are absent at base; the base manifest records that fact explicitly.

## Paired controls

```sh
python3 -I evidence/tools/rule10_controls.py prepare --edition final1 --side base
python3 -I evidence/tools/rule10_controls.py prepare --edition final1 --side final
python3 -I evidence/tools/rule10_controls.py run --edition final1 --side base
python3 -I evidence/tools/rule10_controls.py run --edition final1 --side final
```

Each owner/variant gets a pair using that seal's full exact request set. Body
readings cover ordinary definitions, padding, projections, a generated matcher,
definition-instance unfolding and (in B) polynomial evaluation where present.
Reader positives and instance-lookup/reflexive noninterference positives remain
unsealed-style theorems. Final scopes containing the newly authorized raw
generator/sampler definitions also test their new readers. A explicitly tests
that the evaluation body remains available as excluded notation.

All unsealed probes must exit zero. Each requested sealed-negative declaration
must fail exactly once within its recorded source range; no other diagnostic
is allowed. EOF mask/Name checks must still pass. `control-validation.jsonl`
retains the per-declaration validation, separate from every raw log/result.

## Explicit-unfold scan and summary

```sh
python3 -I evidence/tools/rule10_scan.py prepare --edition final1 --side base
python3 -I evidence/tools/rule10_scan.py prepare --edition final1 --side final
python3 -I evidence/tools/rule10_scan.py run --edition final1 --side base
python3 -I evidence/tools/rule10_scan.py run --edition final1 --side final
python3 -I evidence/tools/rule10_summary.py --edition final1 --base-census-log evidence/logs/rule10/checkpoint1/base-collect/evidence_probes_Rule10_CensusBase.001.log --final-census-log evidence/logs/rule10/final1/final-collect/evidence_probes_CensusFinal.001.log
```

The scan reuses only the inspected pure continuation-list lexer from the
archived scanner. It captures every explicit tactic-list item, source namespace,
opens and declaration status, then checks candidate constant kinds/homes natively
in the exact side's environment. Core and Mathlib candidates are included. It
keeps ambiguous or unresolved items visible for manual disposition; it does not
claim automatic resolution of local elaborator scopes. The whole-file seals
independently check implicit foreign TCSlib reads. Report every foreign-definition
hit and review the unresolved new/touched rows before clearance.

The summary validates raw logs, delivered probe copies and control results,
compares base/final failing declaration sets, prints the target/all-stored axiom
delta, and compares original declaration type/reducibility/simp/instance metadata.
It emits `summary.json` and `summary.md`. Its mechanical boolean is scoped to
those tests; it explicitly does not assert goal completion or clear unresolved
scan rows, the full sweep, admission delta, style lint, or payload manifests.

## Delivery and provenance

Retain the entire tools/probes trees, all snapshots and request records,
manifests, collector/census sources, raw logs and results. Generated baseline
seal/control source files executed outside evidence also have byte-identical
delivered `.lean.txt` copies whose SHA-256 is recorded. Do not include runtime
package or TCSlib object trees in the payload, and never traverse their cache
symlink when staging evidence.

The instrumenter/adapters, collector and census loops derive from the verified
`dl-folds/final-r1/review-evidence.zip` (SHA-256
`203cfa9ae085b3e2485ebc11c6c7c178ae23fd409b9049c22b27cfacb7a96b78`),
whose exact tool sources and provenance are retained under
`evidence/tools/archived-dl-folds/`. The new orchestration is in
`rule10_prepare.py`, `rule10_run.py`, `rule10_controls.py`, `rule10_scan.py` and
`rule10_summary.py`.
