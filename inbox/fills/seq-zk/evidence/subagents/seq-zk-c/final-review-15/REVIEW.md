# Independent read-only final Rule10 provenance review

Reviewer: seq-zk-c. Final source revision d842dc8f681f6b89499129f5b64a50d0e4587935.
Read the issued brief's Rule10/check/report/evidence-completeness requirements and root
final/final-repair plans, request records, generated probes, native logs/guards, reuse
provenance, controls and explicit scan. No Lean, Lake, seals, native probes, source edits,
or root-evidence mutation occurred. Only this authorized review directory was written.

## Findings and disposition

No further provenance blocker was found in the strengthened audit machinery and the
completed records inspected. This is conditional on the lead's final per-cell aggregate
reaching164/164 with no pending cell. The independent review snapshot at
2026-11-15T13:53:48.875113+00:00 had154/164 authenticated cells:
24 final-repair,110 exact revision5 reuse,20 exact CP1 reuse, with10 live revision5 cells
still pending. Those streams were continuing during review. This review does NOT relabel
pending cells as passing; the lead must run the final aggregate to completion afterward.

1. All140 repair-unchanged cells have identical sourceSHA, probeSHA, exact request rows,
   notation exclusions, stored-constant count and closure count between revision5 and
   final. The actual saved probe bytes match the recorded probe hashes in both phases.
   All20 CP1 reuse entries' full current TCSlib source/import-closure hash maps match their
   authenticated historical maps. The final plans form41owners times four variants, with
   no duplicate cell keys. The six-owner/24cell repair frontier independently equals the
   final compiler-reported import-closure dependency frontier of the two changed files.
2. All24 repair native records are present and passing. Every selected native origin
   checked so far has complete native identity/install/mask/EOF guards, matching raw-log
   and request-record hashes, identical final request rows/source hashes, and raw
   diagnostic recount equal to attribution AND guards, using both error forms.
3. The earlier audit-tool summary omissions were reported to the lead and corrected:
   final_matrix_audit.py now independently recounts raw error[:(] diagnostics; the control
   audit checks raw/record hashes, exits, the exact negative line/declaration and the FULL
   singleton native row's identity in final requests, rather than spelling alone.
   The inspected strengthened versions are preserved as reviewed.txt with exact hashes.
   No Lean rerun is required for these metadata validations. The strengthened retained
   control audit already reports PASS.
4. All10 retained native controls were independently validated: five unsealed successes,
   five sealed negatives with EXACTLY one diagnostic at HashSignSensitivity.negative,
   and complete EOF guards, so the positive counterpart also elaborated. Fixture source
   hashes and singleton final native row identities match. Definition-home full-closure
   hashes match current sources; old/final Lean/Mathlib pins match. The archived instrumenter
   tool hashes equal the final manifests. These are retained definition-home controls;
   the report should explicitly identify that reuse and its proof, not imply a fresh run.
5. The unchanged author facade Defs has FOUR inherited error cells, each ten diagnostics
   in the same SIX declarations as the actual issue-base cells. This equality was checked
   against base attributed results, not assumed from a count. Report them explicitly:
   perfectZK_zeroRounds; AbortRetry.attempt_poly; AbortRetry.exists_retrySimulator;
   AbortRetry.statClose_retry; PerfectZKAbort.statZK; negligible_inv_pow_sqrt_div.
   A completed matrix should be described as160zero-error cells plus these4 inherited
   error cells, rather than all164zero. Every old pre-repair failed native cell/log must
   remain delivered and distinguished from its final replacement.
6. Notation boundaries are correct in all four manifests: eval is excluded in A and
   sealed in B; the canonical coe variants exclude only the recorded projection coercion
   FinDist.instCoeFunForallReal, while strict variants retain it. Report both variants and
   every failing declaration, with this distinction. The final explicit scan reports1245
   items (868THEOREM,371LOCAL_OR_UNRESOLVED,6OWNED_DEFINITION),0FOREIGN items. Preserve these
   actual categories; do not describe all items as individually resolved reader facts.
7. Base/final scope needs an explicit N/A explanation:39 new helpers do not exist at issue
   base (independently checked by git ls-tree). The baseline has the owned module and
   unchanged author facade; the final scope has those plus39helpers. Delivery must retain
   every source/request/manifest/tool/raw/result/guard cited by the selected-matrix and
   control reuse records, including superseded failures and historical origins.

## Recommended final report assertions

- Final source commit, final plan164cells, and the effective origin partition20CP1 +
  120revision5 +24native repair, with exact per-cell record/raw/guard links.
- Full source/import-closure and Lean/Mathlib pin equality for EACH reused native origin;
  exact request-row identity and native guards. Do not rely solely on unchanged owner bytes.
-164completed, no pending;160zero-error cells;4inherited Defs cells with all six names and
  ten diagnostics each; strict/coe and eval-A/B attribution, plus preserved old failures.
- Ten retained controls (five pairs), original source hashes/definition-home closure/pins,
  exact native singleton identities, positive success and sealed-negative one-error lines.
- Explicit scan's actual categories and zero foreign items; base helper absence; complete
  delivered paths and hashes, including old raw origins used for reuse.

## Reproducibility and live-input preservation

review.py is an independent READ-ONLY verifier; review.log and independent-checks.json
contain its successful observations. input-hashes.json records every root artifact read.
All consumed JSONL versions are preserved under observed-jsonl: live append-only logs
were recovered ONLY by exact observed-prefix SHA when necessary. No metadata was inferred
or fabricated. input-snapshot-correspondence.json records each exact correspondence.
Root sources and current logs remain untouched. This review receipt is closed for copying.
