# Campaign pulse

The combined statement and independent 31-proof audits each pass **0 blockers,
0 majors, 1 documentation minor and 4 notes** on draft
[#250](https://github.com/Shilun-Allan-Li/tcslib/pull/250). Both documentation
minors are corrected separately and checked. Ten scoped gates now pass; none
approves a merge.

The audited independent proof fill completes **31 obligations in seven modules** at
`f293b63200ee3c6de6e709925f67c4d60fdc7b4a`, leaving **70 owned admissions**. The
same isolated branch/worktree is used; no additional PR branch is created.
The fills are published and their combined Codex proof audit passes. Its sole
F02 overview repair is locally checked at
`af54d28f6d412bc56844e7371e2b0b9b394c494c`, pending client publication. The user
dispatches source work, approves matching and approves all merges.

| Part | Current progress | Remaining work |
|---|---|---|
| DLWE/SIS foundations and sampling | Foundations, exact dyadic laws, bit-noise probability/support/symmetry/mean and common-secret sampling/test laws proved and audited | Efficient uniform family samplers and schedules, source policy |
| Direct Regev symmetric encryption | Algorithms, bounded-error correctness and concrete two-DLWE bound proved and audited | Efficient implementations, uniform message bounds and final existing-game bridge |
| SIS collision-resistant hashing | Core hash/reduction/profile audited; universality, raw collision, evaluator and asymptotic statements pass | New proof fills, pending probability readers/loop disposition, final CRH interface under independent SIS hardness |
| Regev CPA PKE | Algorithms/concrete security statements pass; all four every-coin correctness obligations proved and audited | Concrete-security fills, efficiency and final CPA interface |
| PRGs | All eleven structured/MSB/flat generator obligations proved and audited with complete seed budgets | Efficient family schedules and standard exact-seed asymptotic PRG integration |
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
`ba903806484bcbe7b95a981b3e4dbb68b7f487fd`; only the new comment repair/intake
and source-policy preparation remain local.
Original statement source `17b2a282b545c6ebca3fccc88d518d18ae78f485` and exchange
`64e245b345d908d835030efede1c91312a4e6cce` remain immutable historical inputs.

The exact random-bit/probability reader and counted-loop catalogue proposals
remain unapplied, with affected fills paused under N04. Other remaining admissions
include later independent work too. Source validation/ingestion/approved matching,
physical/native attestations, landing checks and final consumer bridges remain.
No short lattice basis, Gaussian preimage sampler or worst-case/search/decision/
SIS–LWE reduction is introduced. See `fills/04-construction-independent/`.

The next prepared job is `continuation/landing-source-policy/`: Pei16/Wu24
validation and proposed matching for the earlier #236–#239 stack, 161 declarations
in 20 modules at `ec72ed773a690c17ac253707350935cc9e0acb34`. It targets the first
incremental merge path without waiting for #250's remaining construction proofs.
PW10 and later source obligations remain outside that job. No shared registry,
blueprint/dataset, paid pipeline or source approval is changed by preparation.

**Not yet clear to merge — source-policy closure and landing checks remain for
the earlier PRs; #250 also retains seventy admissions and shared-owner holds.
The user approves all merges.**
