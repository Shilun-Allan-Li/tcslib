# Campaign pulse

The combined statement audit passes **0 blockers, 0 majors, 1 documentation minor
and 4 notes** on draft [#250](https://github.com/Shilun-Allan-Li/tcslib/pull/250).
The missed loop-registration sentence is corrected and checked. Together with
the eight earlier scoped gates, nine gates pass; this approves no merge.

The next independent proof fill completes **31 obligations in seven modules** at
`f293b63200ee3c6de6e709925f67c4d60fdc7b4a`, leaving **70 owned admissions**. The
same isolated branch/worktree is used; no additional PR branch is created.
These fills are checked locally and await client publication and their separate
combined Codex proof audit. The user dispatches and approves all merges.

| Part | Current progress | Remaining work |
|---|---|---|
| DLWE/SIS foundations and sampling | Foundations audited; exact dyadic laws, bit-noise probability/support/symmetry/mean and common-secret sampling/test laws now proved | Independent proof audit, efficient uniform family samplers and schedules, source policy |
| Direct Regev symmetric encryption | Algorithms, bounded-error correctness and concrete two-DLWE bound proved and audited | Efficient implementations, uniform message bounds and final existing-game bridge |
| SIS collision-resistant hashing | Core hash/reduction/profile audited; universality, raw collision, evaluator and asymptotic statements pass | New proof fills, pending probability readers/loop disposition, final CRH interface under independent SIS hardness |
| Regev CPA PKE | Algorithms/concrete security statements pass; all four every-coin correctness obligations now proved | Independent proof audit, concrete-security fills, efficiency and final CPA interface |
| PRGs | All eleven structured/MSB/flat generator obligations now proved with complete seed budgets | Independent proof audit, efficient family schedules and standard exact-seed asymptotic PRG integration |
| CCA2 PKE | Secret-matrix lossy/all-but-one mathematics and DLWE column-hybrid statements pass | Supporting fills, pending reader disposition, all-but-one inverse, strong one-time signatures and final CCA2 proof |

The final fresh 144-module scoped sweep passes: zero errors, seventy owned and
seventeen inherited admission warnings, 303.792 seconds. The final axiom probe
records 53.149 seconds. All 31 selected targets and 48 backing contracts use only
standard axioms. Exactly the other seventy source obligations retain `sorryAx`.
The full inventory has 589 constants, including fourteen new compiler auxiliaries.
Two old congruence helpers have earlier originating modules, explicitly recorded;
all 575 previous elaborated level/type representations compare exactly. Style is
0 FAIL/2 unchanged WARN over 41 files; other native warnings match the statement
baseline. No whole-library root elaboration or complete security endpoint is claimed.

Published dependency drafts #236, #237, #238 and #239, and current draft #250,
all target `cryptography/lwe-sis-constructions`. Their integration stays with the
user. The latest remotely verified #250 head at intake is
`c74f629c03933bc4abb4cb24aeff049996cd2b33`; the new fills are not claimed pushed.
Original statement source `17b2a282b545c6ebca3fccc88d518d18ae78f485` and exchange
`64e245b345d908d835030efede1c91312a4e6cce` remain immutable historical inputs.

The exact random-bit/probability reader and counted-loop catalogue proposals
remain unapplied, with affected fills paused under N04. Other remaining admissions
include later independent work too. Source validation/ingestion/approved matching,
physical/native attestations, landing checks and final consumer bridges remain.
No short lattice basis, Gaussian preimage sampler or worst-case/search/decision/
SIS–LWE reduction is introduced. See `fills/04-construction-independent/`.

**Not yet clear to merge — the new 31-proof gate, seventy remaining admissions,
shared-owner dispositions, source-policy work, landing checks and user approval
remain.**
