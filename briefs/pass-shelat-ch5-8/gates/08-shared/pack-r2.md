# Gate 08, round 2: H15 registration and S1 audit repairs

**Closing update, 2026-11-06 PST: Gate 08 CLOSED, round 2 PASS (0 blockers/0 majors/0 minors).**
See `resolutions-r2.md`; the frozen issued pack is at records
`11daf06237ab298fbe8dfdc27b382bd7bd741c08`. The scope below records the issued audit.

**Selected worker: Codex (user).** Return **`gate08-shared-r2-findings.md` as a Markdown file
in the audit chat**; a ZIP may be used for additional required evidence. Do not push to GitHub.
This delivery route supersedes the old push-to-inbox wording in the frozen round-1 inputs.
The user dispatches the audit and merges PRs; no campaign branch is changed by the auditor.

## Pins and scope

- PR: [#227](https://github.com/Shilun-Allan-Li/tcslib/pull/227).
- Repair head: `84f35910912bd3d1cd520beea9469e0ed45ce504`, branch `cryptography/pass-shelat-ch2-4-shared-s1`.
- Repair base: `bee51909a5c581bd61e954d6e1d86c708b4bc804`, incorporating #195 and the H15 records repair.
- #195 was merged by the user as `922fc00cda9ecb3ac0ca8a54fbf2fbe8f50848f4`.
- Original audited S1 head: `c6affb3a92535d3f1de2e0a52c205a84c0cff551`, original base
  `8dcdc8a56382289b5739e13fd18c4d5bd9b67c47`; frozen round-1 records
  `1c623a6c88ecfc6d5e9ae1063c743b0327fcc0ca`.
- The current records commit is pinned by the staged README, revision-qualified manifest and
  dispatch prompt. All full commit hashes are obtained with `git rev-parse`.

The original audit returned **HOLD: 0 blockers, 1 major, 3 minors**, with no false statement
or changed retained statement found. Read the verbatim findings and `resolutions-r1.md` first.
This follow-up audits that disposition and the repair merge. It does not commission the host
proof or expand S1 into the approved deferred cleanup families.

The host proof remains a deliberately authorized `sorry`: Q4 (B) assigns it to a later external
S2 fill, after this gate closes and #227 merges. Do not describe a statement audit as a
kernel-checked proof of that host.

## Repairs to audit

1. **G08-01, major — actual H15 registration.** Verify the H15 row exists in the full pinned
   `machine-library-design.md` §14, not merely in its excerpt or the proposal. Check its public
   contract name/home, statement-only and gate-pending status, external S2 proof assignment,
   four consumer families, repetition/H14 dependency, polynomial-time and tail-length clauses,
   and the statement that this string-function layer exposes no separate machine head envelope.
   Its status must not claim that the host proof is complete or its fill dispatched.
2. **G08-02 — success marker prose.** The contract now describes a nonempty success word whose
   tail holds the value. Its head is not constrained by the public statement. Check the original
   `[false]` counterexample is consistent with the revised prose. The proof sketch may choose
   `true` for its particular witness; that is not an added API guarantee.
3. **G08-03 — retained width.** `natToList_zero_append_drop` now says “the last `W` bits.”
   Verify the formal equation/proof are unchanged.
4. **G08-04 — lexical census.** Inspect the repaired scanner and its regressions. At the original
   pinned base/head, the corrected totals are **506 → 507**. At the base after #195 and this
   repair head, they are **510 → 511**. Both pairs differ only by the host's one `sorry` in
   `Concrete.lean`; #195 contributes its four unchanged deferred efficiency proofs. Do not use
   the old textual 507 → 508 figures as code-token totals.
5. **G08-N1 — disclosed staged counterparts.** G6/G7/G10 public counterparts are approved,
   named cleanup debt under Q2 (A), not an empty no-public-copy result. Verify the payback is
   preserved in clean-up part 2 A/N, including the old restriction theorem's empty-codomain
   case. A new *undisclosed* copy is still a finding; do not require the approved deferred files
   to be absorbed into S1 simply because a counterpart exists.
6. **G08-N2 — type traversal and stronger evidence.** Verify type traversal is outside the
   own-module condition in the collector committed through #227. It still walks definition
   values only for the audited module. Reconcile the fresh candidate lists, additions, seals,
   axiom prints and controls; do not assume their results from the round-1 narrative.

## Statement and source preservation

The repair changes two mathematical docstrings and the collector metaprogram. Source comparison
checks all 1,070 library Lean files against the base/S1 merge union: every file agrees byte for
byte except those two docstrings, whose comment-stripped code agrees. No mathematical proof
strategy or retained statement has been edited by the repair.

The source-header comparison against the current base remains **25 ADDED, 2 REMOVED,
0 CHANGED** public declarations. This is a source-header check, not an independent claim about
every elaborated ambient universe. The original full statement audit and the fresh replay are
separate evidence; report any induced issue you find.

## Check evidence and its limits

Read `evidence-r2/REPORT.md` and the underlying logs. Do not count a failed driver launch as a
proof check or run checks against missing prerequisites.

- Replay: **437/437 from source, zero errors, 437 nonempty fresh oleans; all 364 aggregate
  axiom records unchanged, including the same four `sorryAx` records**.
- Expanded collector/seals/axioms/controls: **90 names, exactly the two expected added pairs; all 15 seals have zero
  touched failures and the same six untouched failures; 146 axiom prints, with `sorryAx` only
  in the host; all 14 controls close unsealed and fail sealed**.
- Import-closure supplement: **13,056 pairs (12,966 active, 90 already irreducible),
  zero touched failures; 17 untouched failing code blocks match the checked base.** Both
  anonymous-only control pairs close unsealed and fail sealed, including the full RSA seal.
  Broad base seals were not rerun; inspect the source-preservation classification and the
  separate historical-cleanup lookup. Earlier invalid harness attempts are explicitly excluded.
- Census: seven lexical regression cases; both pinned comparisons have exactly the one host
  addition. This is a lexical census, not proof elaboration.
- Style: only the six approved size findings in fill-owned files; source-header delta as above.
- The original round-1 base controls remain pinned evidence; their fresh rerun status is stated
  in the round-2 report rather than inferred.

The general gate-04 anonymous-command collector gap remains open tooling debt. The type-traversal
fix is not advertised as a repair of that different gap. Do not turn a list collected from stored
constants into an unqualified claim of coverage of every anonymous command. The import-closure supplement supplies conservative anonymous-command coverage for this
pinned review. No anonymous library command was added by this repair.

The source is [PS10], 3rd ed., January 2010: `Pass–Shelat.pdf` on the campaign branch,
SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`;
book page = PDF page − 12. Existing application citations and frozen statement scope are unchanged.
If running Lean, use the pinned toolchain, a narrowed cache for the needed roots and
`scripts/lean_check_tree.sh`, one module at a time. Never run a library-wide `lake build` or an
unfiltered cache get. The environment addendum remains the host-setup reference.

## Findings and closing threshold

Return `gate08-shared-r2-findings.md` in chat with the exact audited head, verdict, blocker/major/
minor counts and this table:

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Add one disposition for each G08-01–04 and G08-N1/N2: fixed, recorded or unresolved, with evidence.
Describe what you reproduced, what you inspected as supplied evidence, and any limits. Independently verify the 17 supplemental failures are untouched using their pinned source
blocks; distinguish source identity from a fresh base-seal run. Report
any regression or false statement; do not give a blanket approval.

The gate closes at **0 blockers and 0 majors**. Until the follow-up closes, #227 is not clear
to merge. Do not fill `polyTimeComputable_rejectBlocksL`, push a findings file, or change a
campaign branch as part of this audit.
