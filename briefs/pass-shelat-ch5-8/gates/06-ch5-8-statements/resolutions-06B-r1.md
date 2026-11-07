# Gate 06B round 1 resolutions

**CLOSED: PASS, 0 blockers / 0 majors / 5 minors**, at frozen
`3f6db40e1688c4a0bb922c9575dd3bd2157a650b`. The original Codex ZIP and every member were committed before
these resolutions under `findings/gate06B-r1-audit/`. Original ZIP: 32,438 bytes, SHA-256
`7ecad26b31a6f243019230149df5c7d88a690ff86bc4ccd403cfe96c627f5880`.
Verbatim findings: 86,865 bytes, SHA-256
`41e2cbab012ea2f00769c57cb8a7589d47d9557d5e01a5a05b47d132037b1266`.
It arrived as a user-supplied untracked local inbox ZIP; no auditor push/delivery commit is
invented. All five supplied checksum rows verify, and received Python programs stay data:
the maintainer did not execute them.

Issued records/exchange identities remain c81baa7712ab1b43357276ef5df138d02616c9d0 /
5928e06c02b382b63b9b384db89d0458b520f351. The auditor's 129 raw source/20 records/3,419 evidence
entry checks establish input identity; historical native reports are not new kernel runs.

| Finding | Maintainer disposition |
|---|---|
| B-01, minor | Accepted. Generator coins and Bob's two sampler blocks are fresh. Evaluation is deterministic. Only the trapdoor inverter fixes an all-true tape, using its all-tape correctness. Correct the misleading shared verb in the module prose. |
| B-02, minor | Accepted via **prose clarification**, preserving the implementation and theorem statements. The raw decoder checks key/component lengths and prefix equality through total pair projections. It does not separately require successful pair parsing; at `n=ℓ=0`, empty key/ciphertext returns `some []`. State this finite edge explicitly. No stronger malformed-rejection guard is commissioned. Honest correctness and asymptotic claims are unchanged. |
| B-03, minor | Accepted. Appendix C.1/C.1.1 motivates enhanced **inversion**; the predicate/OT argument belongs to Chapter7 §7.3.2. Label the formal Boolean prediction experiment as the explicit strengthened hypothesis used here. Add both source locations and the accessed author-draft versions; do not claim published-edition byte/text/page identity or infer enhanced prediction from an arbitrary bare TDP. |
| B-04, minor | Accepted via explicit deviation. `Good` asserts the correct **first** successful opening for every assignment, and permits multiple openings to the same correct label. The source's stronger unique-opening statement is not the formal conclusion. The cross-opening union bound is a sufficient proof plan for this weaker target; no definition or probability theorem is strengthened. |
| B-05, minor | Accepted. The receiver view's selected mask also depends on the selected sender bit. Take the maximum over all eight triples `(b,a₀,a₁)`, rather than only four `(b,a_(1-b))` pairs. This finite maximum gives a uniform negligible envelope with the existing enhanced-prediction premise. |

The concrete **unapplied** patch is `review-r1-b/minor-prose-corrections.patch`, SHA-256
`20126e560e0c9a4f8fff67026ca892a5257d7890576045909cba50ff81be76ea`. All four files have exact noncomment-byte equality at the audit
source and pass `git apply --check`. It also checks jointly with the disjoint six-file A/D
proposal. No library source has advanced and no post-edit native result is claimed. Apply
and refresh source-matched checks during final integration, after the outstanding audit result.

## Retained statement qualifications

Five-message OT retains canonical-only `henc`, explicit evaluator efficiency `hH` and the
sampler-coin enhanced-hard-core premise. Canonicity is derived. The simulator gets only its own
input and ideal output. Security includes the other party's output in the joint experiment,
with simulator-before-distinguisher and uniform-over-input negligible bounds.

Composition remains the specialized nonadaptive pre-call model, with main efficiency for all
right-length answers and the positive-main-round premise. Exact phase identities cover zero
calls/subprotocol rounds without silently dropping that output-alignment condition. Real Yao
retains sink outputs, conditional output-label distinctness, actual bit-tape/XOR-shift sampling,
uniform polynomial circuit bounds and joint security of the two shared-key PRF families.
Its quantitative error is gate/output-count dependent, not negligible for unbounded circuits.
No existence result from bare one-way TDPs alone is claimed.

All thirteen direct admissions and their five derived wrappers remain disclosed. The audit
approves definitions/statements/sketches and the scoped short correctness/phase proofs;
it does not complete the security, simulation or efficiency fills. The common inherited
Rule10 failures/equation references remain failed/debt observations, not exclusions or passes.

## Source and execution limits

The auditor accessed the exact supplied PS10 §6.2 and the official Goldreich Chapter7 and
Appendix drafts firsthand. Chapter7 browser content was readable (version3.2, 2July2003),
but its raw PDF hash was not independently recomputed. Appendix raw bytes/hash matched.
Published-edition equivalence remains unverified. Lindell–Pinkas ECCC revision/author and BMR
comparisons support the stated architectural attribution with their exact report limits;
no journal-version identity is inferred. Other prongs' Goldreich/PSV comparisons remain separate.

Neither the external audit nor this intake ran Lean/Lake. Finite Python models corroborate
semantics, not cryptographic hardness or Lean proof completion; received scripts were not
executed by the maintainer. Root-export elaboration and the combined post-S2 target tree
are not attested by this frozen audit. C and coordinated final source reconciliation remain.
No new fill/follow-up audit is prepared or dispatched by this closure.

Internal review in `review-r1-b/internal-review/` independently assessed the report and all
12 patch hunks, with no additional blocker/major. It verified the six ZIP member identities
and exact noncomment preservation; no native or delivered-program execution was performed.

**Not yet clear to merge — 06B is closed; #232 still needs 06C and final source reconciliation.**
