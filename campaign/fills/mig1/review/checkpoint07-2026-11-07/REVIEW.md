# MIG-1 cp07 incoming checkpoint review

2026-11-07; bounded static review by Codex. **Not yet clear to merge.** This is a
partial recovery checkpoint, not the final fill. The original 17 targets and two
approved new forwarding theorem bodies are proof-filled in source, but rule-10
repairs, factoring dispositions and final validation remain outstanding. No gate
closure, fill acceptance, or fresh elaboration is claimed.

## Receipt and exact cumulative scope

The original ZIP and root reports are preserved byte-for-byte under `original/`
and `reports/`. `receipt.json` and `zip-inventory.json` record the full receipt.

- ZIP: **1,614,062 bytes**, SHA-256
  `22d64f8fa9de04e3c82ab3a8a79c06b6a1679917509e409de7a78d3b4b141c9f`.
- **770 members, 739 regular files, 738/738 payload checksums verified**. Names,
  absolute/traversal paths, case/Unicode/rename collisions, entry modes, symlinks,
  sizes and CRC were checked before extraction. No uncovered payload file or
  special entry. Every extracted Lean filename ends in `.lean.txt`; no delivered
  script or proof was executed.
- Exact base is `83ac315ed9e7089466bd16a32f3b71fbadc556d2`. Delivered head metadata is
  `cbfdba8102e6a5d956a1fdd2be7518b490a5abac`.
- All eleven cp03 snapshot hashes were checked against the earlier immutable
  comparison receipt. Reversing its three reviewed textual patches in memory,
  then replaying them, gives an exact round trip. Applying all **five cp07 patches**
  from that recovered base reproduces every supplied cp07 source byte with exact
  hunk/context matches and owned paths only. No Git command or payload tool was
  used for this reconstruction. See `compare-source.py` and `source-comparison.json`.
- Separately, the root maintainer verified the Git bundle, imported only a delivery
  ref, resolved the full head, and checked all eleven snapshots against actual
  object blobs. That is the root's distinct executed check in
  `../checkpoint07-git-objects/receipt.json`, not an execution claim by this reviewer.

The independent source freeze finds **357 → 354** public declarations: exactly
`Turing.FinTM.pairMapSndTM`, `_computes`, `_spaceUsed` added, and exactly the six
permitted Catalog canonical rows removed. No other public/header/visibility/home,
relative order, existing definition body or witness-table change was found. The
only import additions are the two approved ones: `Mathlib.Algebra.BigOperators.Fin`
in Simulation and `Build.Primitives` in Catalog. Existing public proof changes: **57**,
plus the two new forwarding proofs. No proposed reader API was silently added.

All **17** target headers match the pinned base and their bodies contain no source
admission. All three forwarding declarations match the statement-gated contracts,
including time coefficient **22**, payload-space coefficient **one**, malformed-input
behavior, monotonicity assumptions and the absence of a time premise for space.
The two new proof bodies are filled. Remaining source admissions are only:

- `WordRAM.WordSizeComputable.mono`
- `WordRAM.wordSizeComputable_logSpace`
- `WordRAM.wordSizeComputable_of_spaceConstructible`

This is a source census, not an unfiltered compiled declaration/auxiliary census.

## Progression and F-D work

Against cp03, only Primitives, Catalog, CertShell, CodeSimulator and WordSize change.
Against cp05, **only Catalog, CertShell, CodeSimulator and WordSize change**. Primitives,
Loop and all F-A files are byte-identical to the prior reviewed checkpoints. The
corresponding fifteen final seal source/output/list files are also byte-identical
(`inherited-evidence-comparison.json`). Earlier omissions and failed seals therefore
remain live obligations; the short cp07 report does not supersede them.

- Catalog's private count is **392 → 36**, with **356 private retirements**, no new
  private declaration and no surviving private-body change. The removed source
  families are the obsolete `f2_`, `a2_` and `catalog_redirect*` copies. The worker's
  pruning log reports 8,202 deleted lines; this review independently confirms the
  declaration identities/count, not a semantic reachability theorem from that log.
- Nineteen public space-row proof bodies change. The report's twenty-row list also
  includes `computesFunInTime_pairEncodeFixed_spaceUsed`, which was already the
  corresponding corollary and is unchanged. The new rows mostly invoke the named
  same-home specs and published generic time/space/cardinality facts. The redirect
  row now uses `spaceUsedByTape_eq_card` and `mem_visitedByTapeHead_iff` rather than
  re-unfolding the whole trajectory measure.
- All six permitted canonical public rows are gone. CertShell's private
  `cert_prepare_exists` re-points one copy and three transfers; CodeSimulator's
  `MachineFormat.canonPreserveInstall` re-points one copy. They use framed contracts,
  the published canonical endpoint lemmas, and tape/head equations. Exact row times
  `2*length+2` are bounded by the previously used `3*length+3`; public constants and
  controller definitions remain unchanged. The empty-word case is retained by those
  framed contracts. The new state-premise `rfl` reads below still need repair.
- WordSize changes one documentation line only: the Catalog length-counter row now
  starts at **1980**, replacing stale line 4318. All WordSize declarations are unchanged.
- The cp05 forwarding implementation/move review carries over by exact source hash:
  32 moved declarations match their old Catalog sources modulo recorded renamings;
  executable state/table definitions are preserved. Only `poly_space` and
  `fwdMap_space` proof bodies had substantive reuse changes. cp07 removes their old
  Catalog homes. This is inherited independent review evidence, not a fresh proof run.

The supplied final retirement scan reports no exact retired names in `TCSlib/`; the
owned source snapshots likewise contain none. The brief's original candidate list
placed all code consumers in the three reviewed files. An exact whole-tree grep at
the final landing head remains a final check. The worker also lists four live
non-Lean references across `machine-library-design.md`, `campaign/backlog.md` and
`campaign/design/plans/AroraBarakChapters3-4Plan.md`; these are maintainer follow-up
outside the worker's owned proof files. Historical records must remain historical.

## Required repairs and dispositions

### New F-D boundary reads

**Catalog tape-count readings need a legal public route.** The newly written
constant-space corollaries for `idTM` (1927), `constTM` (1942), `prependTM` (1960)
and `pairValidTM` (2120) pass `rfl` to the zero-tape-space theorem, reading the
foreign witness's `.k = 0`. The `pairDup` (2158) and `incFixed` (2259) rows do the
same, and the three pair-extraction rows (2084, 2102, 2137) use `change 1 * …`.
The poly-bits row (2027) obtains `(polyBitsTM 0 e).k = 0` by `subst; rfl`.
These are actual definitional readings in source; **no F-D seal was run here**.

Distinguish repairs before requesting further API. For the five positive linear
space bounds (three extractors, pair duplication and fixed increment), absorb the
opaque witness tape count into the existential coefficient instead of reading a
fixed count. The frozen statements permit this routine choice. The poly-bits
zero-coefficient branch can plausibly use the existing constant-machine space row
rather than inspect `polyBitsTM.k`. Those are candidate repairs, not checked proof
scripts. Four genuinely constant-space cases may instead need existing or approved
same-home zero-space operational facts. No explicit suitable public fact or `simps`
attribute was found in the inspected canonical source, but **compiled/generated
name absence was not tested**. The root has a separate peer assessment of that
unapproved scope; this checkpoint does not authorize extra API.

**Five new canonical-seam state premises reduce a foreign definition.** Each new
CertShell/CodeSimulator copy/transfer contract call passes `rfl` for
`(Cfg.ofWords .sweep w).state = some .sweep`. The existing published
`Cfg.ofWords_state` should replace that argument. Tape and head premises already
use their public equations. This is a mechanical reuse repair, with no new API
indicated, and should be covered in the F-D seals.

### Inherited obligations, unchanged by cp07

The previously reviewed files and evidence are byte-identical, so the following
remain unresolved:

- Composition/Wrappers' `branchTM` shape/operational exclusion and the configuration
  reader boundaries (`leftCfg`, `rightCfg`, `captureCfg`), including implicit reads.
  **Latest user ruling communicated by root:** the existing nineteen proposed reader
  theorems are now approved. Their implementation, actual consumer repairs and
  complete seals are still separate work; approval alone does not repair cp07.
- Loop's seal still covers **15 regions rather than all 16 changed/new surviving
  declarations**: `loopHost_input_rewind` is omitted. Restore coverage and rerun.
- The supplied Primitives seal still records **18 errors**. The cp05 independent
  review maps these to moved `fwdMap_*` and `poly_space` proofs. New public forwarding
  proof success cannot be inferred from that incomplete seal.
- `pairEncode` and `pairDecode` are missing from the Primitives seal/control lists,
  despite explicit foreign-definition arguments and a singleton `rfl` read in the
  new/moved forwarding material. Use the existing pair-encoding equation and pursue
  the public decoder route identified in the separate assessment; no new decoder
  API is established as necessary by this static review.
- Explicit Mathlib `SignType.cast` simplification arguments remain in moved
  `poly_step`; use its named coercion equations. The other native-operation,
  initialization and `controlAction` repairs reported by cp05 also remain.
- Complete per-kind MIG-24 dispositions are still needed. T2/its cross-file
  first-entry candidate, T2b and T3 were previously reported pending, and their
  source files do not change here. T3's same-home call-bank duplication remains.
  T6's three pair-projection space proofs remain separate template arguments rather
  than a shared helper; factoring their generic time-to-space argument can also
  avoid the extractor tape-count readings. T5's canonical retirements and consumer
  re-points are done, with the pre-existing common trace visible in surviving framed
  rows; this does not replace the complete requested per-kind disposition. No new
  debt acknowledgment follows from this partial checkpoint.

No external audit verdict or new severity count is assigned by this internal
checkpoint review. These are pre-landing obligations, not a claim of a false
formal target or a request to change its statement.

## Supplied validation and what is still missing

The following are **worker-produced receipts**, inspected as data:

- `fd1.summary`: Catalog exit 0, zero errors/admissions, 33 warnings.
- `tail-fd1/summary.log`: all 34 listed bootstrap-tail modules exit 0; only the
  unchanged three WordSize admission warnings. Its header honestly identifies the
  pre-commit dirty tree; it is not the maintainer's current-campaign replay.
- `fd2.summary`: CertShell exit 0 with one warning; WordSize exit 0 with its three
  inherited admissions. The CertShell edit between tail/fd2 was prose.
- The worker freeze agrees with this independent source freeze. Its order check
  reports 641 distinct modules, no missing dependencies, and Primitives before Catalog.
- The cumulative F-A/F-C/F-B axiom logs cover the filled targets and the new forwarding
  theorem proofs with standard axioms. F-D axiom walks and the compiled census are
  explicitly not yet supplied.

The included final-sweep summary has **six completed successful rows**, no final
footer, and partial raw output for the next module. It does not certify a
641-module sweep. Screens were running at packaging time; no completed final
base/head comparison is in this checkpoint. The report explicitly leaves F-D seals,
Primitives repairs, F-D axiom walks, compiled census and policy lint outstanding.
A final delivery, complete validation receipts, revised reached-definition/coverage
inventory, final factoring disposition and later current-campaign replay/gate are
still required. No final zip was reviewed in this task.

This review inspected the new F-D deltas and relevant contracts, used mechanical
header/patch/body comparisons for the cumulative source, and inherited the detailed
cp03/cp05 findings only after verifying byte identity. It did not reread every
unchanged proof or validate delivered Git pack objects. No Lean, Lake, cache,
screen, Git, push, delivered-script execution or actual source edit was performed.
All outputs are restricted to this new review directory.
