# Gate 08 round 2: maintainer verification

**Maintainer checks complete; external follow-up not dispatched.** This report records maintainer checks, not an external closing
verdict. Gate 08 remains on HOLD pending the selected Codex follow-up.

## Revisions and scope

- Checked PR #227 head: `84f35910912bd3d1cd520beea9469e0ed45ce504`.
- Checked campaign base: `bee51909a5c581bd61e954d6e1d86c708b4bc804`, including the user's
  #195 merge `922fc00cda9ecb3ac0ca8a54fbf2fbe8f50848f4` and H15 registration.
- Original audited base/head: `8dcdc8a56382289b5739e13fd18c4d5bd9b67c47` /
  `c6affb3a92535d3f1de2e0a52c205a84c0cff551`.
- Local dates use 2026-11-06 PST; resource logs use UTC (2026-11-07).

The merge incorporates #195 without modifying its library source. The repair changes only two
mathematical docstrings and the collector's referenced-type traversal. All 1,070 library Lean
files match the base/S1 source union byte-for-byte, except the two comment edits whose
comment-stripped code is identical (`merge-source-preservation.log`). The source-header diff
against the checked base remains 25 ADDED, 2 REMOVED, 0 CHANGED public declarations
(`statement-diff-vs-current-base.tsv`). This header comparison does not independently inspect
ambient elaborated universes. Original statement-audit evidence remains the frozen round-1
findings; the host proof remains explicitly authorized `sorry` for external S2.

## Environment and cold replay

Native arm64 macOS, Lean 4.25.0 and the manifest-pinned Mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. All present package checkouts match their manifest
URLs and revisions; the four absent documentation packages are not needed. The cache request
was narrowed to 144 named roots (`roots.txt`): zero downloads, 3,086 existing cache files
decompressed. A root import probe passed; no zero-length package oleans were found.

The preflight records `vm_stat` and `memory_pressure -Q`; free + inactive + speculative pages
times the native page size is a macOS headroom proxy, not Linux MemAvailable or a cgroup limit.
The recorded machine had approximately 5.5–6 GiB of that proxy available and ample disk.
The unmodified DetMod prerequisite ran for about 13 minutes, then passed; an intervening
own-process resource observation showed active CPU use and healthy native headroom. No
module was killed or given a self-imposed timeout.

**Cold replay: passed, 437/437 entries, zero errors and 437 nonempty fresh oleans.** `bootstrap.py` verifies every source against the checked head and
runs `scripts/lean_check_tree.sh` sequentially into the fresh dedicated tree
`.lake/ps-maintainer/oleans-gate08-r2`. `order.txt` contains 437 entries, comprising prerequisites,
100 affected modules, and `audits/pass-shelat/Checks`; `downstream.txt` preserves the UP/DOWN
classification. `source-sha256.txt`, `logs/bootstrap.log` and `logs/modules/` retain exact inputs,
return codes, timestamps and native maximum resident set size for each check.

The replay took 2,414.782 seconds, with peak per-module RSS 3,150,184,448 bytes. All 364
aggregate `Checks` axiom records agree with the original S1 head: no added, removed or changed
sets, and the same four `sorryAx` records (`replay-summary.json`). The post-run native memory
snapshot reported 63% free; the recorded final process had already exited, so that snapshot
does not establish a live CPU/RSS value (`logs/final-resource-check.log`).

The first driver attempt failed on its log path before starting Lean
(`logs/driver-attempt1.log`); that attempt is not a proof check.

## Expanded referenced-type collection and probes

A separate probe tree contains only 272 completed TCSlib oleans copied from this run. Every
copied object's SHA-256 was checked. Closure, Arithmetic and Concrete were then rebuilt from
the checked source into the copy and matched byte-for-byte before use (`copied-tree.json` and
the three `logs/copy-verify-*.log` files). Dependency trees were not copied. Each tree runs at
most one Lean process; the copied tree permits probes while the cold replay continues.

`checks-r2.py` uses the collector fixed through PR #227. The union has **90 names**, adding
exactly `(DiscreteLog, bitsToNat)` and `(RSA, primeStr)` to the old per-module pairs and dropping
none. All **146 touched-declaration axiom prints** contain only `propext`, `Classical.choice`
and `Quot.sound`, except that the authorized host alone also uses `sorryAx`.

All **15 whole-file seals** reproduce zero touched-declaration failures: ten close, and five
files contain six known untouched failing declarations (DiscreteLog emits several diagnostics
for one declaration). The failures are `primesPairEquiv_apply_val`,
`ExpGroupGen.FullLength.exists_fullLengthExcept`, `exists_plantFactorer`,
`rabinCollection_index`, `rabinBlumTrapdoor_index` and `uexp_mono`.
All **14 controls close unsealed and fail sealed**, including the new primeStr control.
See `expanded-checks-summary.json`, `axioms-touched.tsv`, `seal/`, and the corresponding logs.

Original round-1 base controls were **not rerun** in this follow-up. Their frozen source and
results were independently checked by the original auditor; the merge-preservation comparison
establishes that the relevant unchanged library source remains the base/S1 source union.
The first expanded-check driver stopped because its expected label omitted the enclosing
namespace of `exists_fullLengthExcept`; the corrected driver retained completed checks only
after exact probe-source validation (`logs/checks-driver-attempt1.log`). No failed proof was
reclassified as a pass.

## Anonymous-command coverage

The final supplement covers **13,056 module/name pairs: 12,966 active local seals and 90
already globally irreducible pairs**. It enumerates ordinary foreign TCSlib definitions from
each audited file's complete source import closure, retaining the same instance/reducible
exclusions and leaving `PolyExpr.eval` and `glNeed` unsealed. Five files close; ten contain
**20 diagnostics in 17 untouched declarations, zero touched failures**. Every failing
code block matches the checked base after comment removal; following namespace commands are
excluded from the block comparison. This is source preservation, **not a fresh base-seal run**.
The original narrower six-failure/base-control evidence above and this supplement are distinct.

Both anonymous-only control pairs close unsealed and fail sealed: one seals primeStr alone,
and the other uses the actual complete RSA import-closure seal. The sole foreign-definition
read in each probe occurs in its anonymous `example`. The candidate collection is independent
of stored-command reads, so this covers the anonymous-command gap for this pinned review;
it does not repair the general collector implementation.

The authoritative supplemental probes are **`conservative/ClosureVerified*.source.txt`** and
**`logs/ClosureVerified*.log`**. They resolve numerical and hygienic private Names against the
imported environment, require an unambiguous exact Name, skip reapplying attributes to names
already irreducible, and verify every candidate's status. Any diagnostic in the seal command
is rejected before a proof failure is classified. `conservative-summary.json` and
`conservative-failure-preservation.json` retain counts, return codes, declarations, source
hashes and that command-diagnostic check. `compare-conservative-failures.py` reproduces the
code comparison. The historical cleanup lookup matches 15 of these 17 rows to the 764-row
inventory; the other two are recorded for issue-time reconciliation in the tooling ledger.
That lookup is data, not a fill issue or a claim that old line numbers remain current.

Earlier harness attempts are retained in `logs/conservative-driver-attempt*.log` and their
separately named probe sources. They exposed empty-list handling, numeric/hygienic Name
rendering, misqualified environment/control names, and redundant attributes on already
irreducible definitions. **Those runs are not counted as valid supplemental seals.** The
completed candidate collection was reused only after exact saved-source validation. The final
run has no seal-command diagnostics; no invalid harness result is promoted to a proof pass.

## Census, registry and style

- G08-01: H15 exists in the actual root registry. `H15-registry-extract.md` includes exact
  source rows and the full registry's SHA-256; the auditor must verify the pinned root file.
- G08-02/03: the two docstrings now match the unchanged formal contracts.
- G08-04: seven lexical regressions pass. Original counts are **506 → 507**, and after #195
  **510 → 511**. Each pair adds exactly one `sorry`, in Concrete. The four-count baseline
  increase is #195's deferred efficiency proofs. `census-summary.json`, revision-qualified
  census outputs and `census-regressions.log` retain the evidence. The old textual counts
  remain historical, labelled in the original report; they are not code-token counts.
- Style lint returns 1 for exactly the six approved fill-owned file-size findings, retained
  in `logs/style-lint-head.log`. This is an accepted exception, not a clean lint exit.

**Not yet clear to merge — the external follow-up audit must close.**
