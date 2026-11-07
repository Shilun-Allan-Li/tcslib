# MIG-1 cp05 incoming checkpoint review

2026-11-07; internal review by Codex. **Not yet clear to merge.** cp05 is a cumulative
partial checkpoint. All 17 original targets and the two approved new forwarding specs are
proof-filled in source, leaving only the three frozen RAM admissions. Its Primitives seal
explicitly fails, and this review identifies further omitted foreign definitions. No fill
acceptance, gate closure, or independent elaboration is claimed.

## Receipt, package, and freeze

Original ZIP and REPORT are preserved verbatim in `original-zips/` and `reports/`.
[receipt.json](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoint05-2026-11-07/receipt.json)
and `cp05-inventory.json` contain the independent inventory and hashes.

- ZIP: 1,455,413 bytes; SHA256
  `5744d37d6144ca803134ba247144c3686acca1f0f581f35bacdd45cbc032385c`.
- 663 members, 637 regular files, **636/636 supplied payload checksums pass**. Safe-name,
  duplicate/collision, symlink, size, and CRC checks pass; no uncovered payload file.
  Payloads were read before extraction. Every extracted Lean filename ends in `.lean.txt`.
- Relative to cp03, **only Primitives changes**: seven existing public proof bodies,
  three authorized public additions, 32 private additions, 18 private retirements, and
  no surviving private body change. The old captured-output map, private pair-duplicate
  implementation, and its unreachable payload lemma are retired.
- Against pinned base `83ac315ed9e7089466bd16a32f3b71fbadc556d2`, public count is
  357→360, exactly the three forwarding additions. No public removal, complete-header,
  visibility, home, surviving-order, existing public definition-body, witness-table, or
  extra import change. The approved Simulation import is the sole cumulative import
  addition. No unapproved reader API was added. Cumulative existing public proof changes: 38.
- All four cumulative patches reconstruct every supplied source snapshot exactly, with
  exact hunk/context matches and owned paths only. Prior changes are preserved; patch
  subject numbering changes for the four-patch series. Bundle header agrees with the
  pinned prerequisite and delivered HEAD metadata
  `f74d8c0ed8ac1f452a2026e9b1204f0442f40456`; pack objects were not imported or validated.

No Git command was run. As for cp03, base bytes were recovered from immutable cp02 records
by exact reverse/forward patch reconstruction and snapshot-hash checks. See
`source-comparison.json`, `patch-consistency.json`, and `cp03-to-cp05-source.diff`.

## Approved forwarding contract and implementation

Independently checked all three additions against `forwarding-map-contract.lean.txt`:

| Addition | cp05 line | Result |
| --- | --- | --- |
| `Turing.FinTM.pairMapSndTM` | 3417 | Complete header and definition body identical |
| `Turing.FinTM.pairMapSndTM_computes` | 3427 | Complete header identical; proof contains no admission |
| `Turing.FinTM.pairMapSndTM_spaceUsed` | 3487 | Complete header identical; proof contains no admission |

This preserves time coefficient 22, coefficient one on payload space, malformed-input
behavior, monotonicity hypotheses, two buffers, and the absence of a time hypothesis in
the space statement. All 32 moved private declarations were compared with their actual
Catalog sources modulo the explicit private/home renamings. All executable definitions,
state constructors and the instance match. Only `poly_space` and `fwdMap_space` have proof
changes beyond those renamings: published head/cardinality bounds replace the old generic
derivation, and `Fin.sum_univ_add` replaces the private sum-equivalence implementation.
Catalog remains unchanged at this checkpoint, so F-D must remove its obsolete copies.

The existential pair-duplication row now uses canonical `pairDiagTM` with witness constant
5 instead of the retired private machine's 4. Its public statement still quantifies `c`;
the replacement is explicitly authorized by the brief, and `4n+5 ≤ 5(n+1)` explains the
new witness. This is a routine authorized witness choice, not a changed frozen public
coefficient or a request for new design approval.

## Confirmed rule-10 findings

1. **The reported failed seal is real evidence of incomplete work.** All 42 changed/new
   Primitives declarations appear in individual sealed regions, and removing only seal
   wrappers restores the submitted source code. The supplied output records exit 1 and
   exactly 18 errors, all mapped independently to moved private `fwdMap_*` proofs or
   `poly_space`. `evidence-check.json` lists each owner and diagnostic. The reported
   native-operation/initialization/control-action repairs remain required. Explicit
   `MultiTapeTM.step` / `Action.apply` arguments also remain throughout `poly_step`
   ([2254 onward](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoint05-2026-11-07/cp05/fill-mig1-mega-cp05/source/TCSlib/Complexity/TuringMachine/Build/Primitives.lean.txt:2254)).

2. **`pairEncode` and `pairDecode` are omitted from that seal, despite new reads.**
   New public `pairMapSndTM_computes` explicitly unfolds foreign `pairEncode` at
   [3474](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoint05-2026-11-07/cp05/fill-mig1-mega-cp05/source/TCSlib/Complexity/TuringMachine/Build/Primitives.lean.txt:3474);
   moved `fwdMap_finish` does so at 3034. Moved `fwdMap_parse` explicitly unfolds
   `pairDecode` at 3060, 3076, 3089, 3094, 3100 and 3107, and reads its singleton case by
   `rfl` at 3068. Both are ordinary definitions in Encoding and absent from the displayed
   seal/control lists. Thus “new public proofs are not among the failures” applies only
   to that incomplete list. Use `pairEncode_eq`, refactor the decoder-dependent argument
   through the existing public interface, and expand the seal, simplifier suppression,
   and paired controls. The separate
   [decoder assessment](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/pair-decoder-assessment/README.md)
   gives an unelaborated route using the public success/inverse/failure-shape theorems;
   no new decoder API is forced by that source analysis. It does not repair or seal cp05.

3. **Explicit Mathlib-definition arguments remain too.** Moved `poly_step` passes
   `SignType.cast` to simplification at 2272, 2274, 2289, 2313, 2315, 2329, 2331, 2344,
   2347, 2352 and 2361. It is a `def` in Mathlib `Data/Sign/Defs.lean:206`; named coercion
   equations are already available. This falls under the explicit-argument rule even
   though Mathlib definitions need not be sealed against ordinary definitional reduction.
   It is a mechanical reuse repair, not a public API decision.

The report mentions a Primitives argument scan but supplies no corresponding Primitives
scan output; the findings above come from independent source inspection. Complete the
definition-argument and reached-definition inventory rather than treating the 18 errors as
the entire repair list.

## Evidence, factoring, and remaining status

The supplied 17-name axiom log covers all nine new/changed public proof bodies in this
batch, plus eight unchanged dependency/composite rows. Every listed result uses only
`propext`, `Classical.choice`, `Quot.sound`. The 35-module bootstrap tail records zero
failures. Final `fb4.summary` records exit 0, zero errors/sorries, and 58 warnings; `fb1`
is a retained failed intermediate attempt. These are worker-produced logs, not fresh
maintainer checks. Paired controls are byte-identical to reviewed cp02/cp03 controls and
do not cover the two newly identified encoding definitions.

F-D retirements/consumer re-points, Primitives repairs, and MIG-24 T2/T2b/T3 dispositions
are explicitly pending. The prior configuration/capture-reader and `branchTM`
shape/operational gaps and cp03's omitted `loopHost_input_rewind` seal region also persist:
all their source files are byte-identical to cp03. They must remain on the cumulative
obligation list even though this checkpoint's short “Remaining” section does not repeat
them. Final assigned factoring dispositions, including Primitives' T1 scope, still need
an explicit account. No new debt acknowledgment follows from this partial delivery.

Policy lint remains unrun. As prose follow-up, check the moved long induction/case proofs'
sketches, especially `fwdMap_suffix`, `fwdMap_backA`, and `fwdMapSetup_head_step`, whose
nearby comments mainly state their conclusions; remove “commissioned” from the new
controller docstring. These are source-quality follow-ups, not design changes.

Compiled auxiliary census, screens, full 641-module sweep, and maintainer replay remain
NOT RUN. Source admissions are exactly the frozen
`WordRAM.WordSizeComputable.mono`, `WordRAM.wordSizeComputable_logSpace`, and
`WordRAM.wordSizeComputable_of_spaceConstructible`.

I reviewed the new public proofs, changed proof deltas and failure/ownership contexts;
the large verbatim moved family was checked mechanically against its source rather than
reread in full. No Lean, Lake, screens, cache operations, Git, pushes, payload execution,
external messages, or writes outside this new review folder were performed. Prior review
folders remain unchanged; cp07 is reviewed separately by another agent.
