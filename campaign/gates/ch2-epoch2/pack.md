# External audit pack — Chapter 2, epoch-2 fill gate

Audits the **proofs** of the ten epoch-2 targets — eleven public theorem
names (the ledger counts the Theorem-2.6 reverse inclusion and the
equality corollary as one target): `NP_subset_EXP`; `HALT_NPHard` and
`HALT_not_mem_NP`; `ntime_poly_subset_NP`; `NP_subset_iUnion_NTIME` with
`NP_eq_iUnion_NTIME`; `mem_NP_iff_exists_length_le`;
`timeConstructible_poly`; `TMSAT_mem_NP`; `TMSAT_NPHard`;
`TMSAT_NPComplete` — filled by **ten Codex commits across nine zip
deliveries** (four checkpoints, four continuations, B2) with **386 new
private declarations** in five files: `ClassNP/{EXP, Nondeterminism, NP,
Reductions, TMSAT}.lean`. With this gate the Chapter-2 ledger stands at
38 of 59 original admissions proved, and Theorem 2.6, Exercise 2.1, the
HALT pair, and Theorem 2.9 are end-to-end machine-checked.

The **statements are not in question here**: all eleven were frozen at
the phase-1/2/3 statement gates (`audits/ch2-phase{1,2,3}-*`), and the
span-wide freeze is independently attested below. This is the fill-epoch
proof audit in the mold of the epoch-1 and library fill gates: proof
correctness and helper hygiene against the frozen statements, the
inherited invariant tables (carried verbatim in the attached briefs),
and the audited machine-construction library. Gate closes on **zero
blockers/majors**. Record findings in `audits/ch2-epoch2-findings.md`.

**Evidence separation.** Out of scope: the machine-construction library
itself (`Build/`, two closed gates — consult `audits/ch1-infra-resolutions.md`
and `audits/ch1-libfill-resolutions.md`; its files are in the repository,
and the fills' *consumption* of its contracts is very much in scope); the
bridge `timed_universal_quantitative`'s statement and discharge
(sanctioned by 2D's bridge protocol, proof-audited at the infra gate —
its *consumption* by the TMSAT budget chain is in scope); the remaining
21 admissions (5 epoch-3 padding, `EXP_subset_NEXP`, 15 E3/E4 statement
layer — later epochs); the model files (attached as the definitions the
proofs elaborate against, audited in their own gates, not for re-audit).
Both continuation hosts disclosed a `/proc/<pid>/exe` shim; it never
entered the repository and is superseded by the maintainer's independent
fresh sweeps on an ordinary host.

## Maintainer-side integration attestations (verify or challenge)

The full evidence is the attached
`audits/evidence/ch2-epoch2/span-attestation.md`; summary:

1. **Whole-span freeze.** Over `f317f0c7` → `2e176f60`, the net diff of
   the five owned files deletes **exactly the eleven target `sorry`
   lines**, six append-only docstring tail splices, and 2C's one
   recorded token-identical statement-line rewrite — nothing else; and
   the name-level public surface is **identical everywhere except the
   one sanctioned bridge addition** in `TMSAT.lean`. Import drift:
   `Build.Primitives` per batch (route-forced) plus five disclosed
   modules, all order-legal.
2. **Per-delivery verification** (each recorded in the decision log at
   integration): checksums for all nine archives; per-patch
   deleted-lines audits; byte-identical format-patch replay in isolated
   worktrees before every `git am -3`; B2's attested source SHA-256
   reproduced; the three maintainer integration commits touch no source.
3. **Elaboration.** Fresh-olean sweeps at every integration, zero
   `error:` lines, admissions stepping 32 → 29 → 23 → **21**, each step
   predicted before the sweep and matched exactly. Final 57/57 sweep
   attached (`ch2-e2cont-B2-integration-sweep.log`).
4. **Axioms.** The maintainer closure traversal (attached committed
   program `audits/programs/ch2-e2-ClosureAxioms.lean`; attached log):
   all twelve closure names print at most the standard triple with
   **empty admission-root sets**; Chapter-1 headline and library
   regressions unchanged; `EXP_subset_NEXP` at exactly its own root.
   Intermediate traversals at both earlier integrations confirmed every
   interim root exactly as disclosed (the A/C cluster funneling through
   the single admitted private `enumMachine_contracts` before its
   continuation discharge).
5. **Policy.** Lint in scope: **0 FAIL, 3 WARN** — the recorded size
   exceptions (EXP 2,887 / Nondeterminism 2,627 / TMSAT 1,908 lines),
   each justified at integration under exclusive single-file fill
   ownership. Sketch docstrings extended append-only throughout;
   attributions intact.
6. **Deviations on record** (all disclosed at integration): all four
   initial deliveries were partials invoking their briefs'
   continuation provision; 2C's cosmetic statement-line respacing;
   both continuation hosts' cache-setup recoveries without touching
   pins; B2's `TAR_OPTIONS=--no-same-owner` cache recovery.

## Dispositions requested

* **E5 — dedup of superseded checkpoint privates.** The checkpoint
  strata contain helper families superseded by the continuations'
  library-based routes (A's `enumCarry*`/`enumCapture*`/`enumLoop_run`
  cluster; C's `prefixTM`/`fixedPair`, their promotion requests subsumed
  by library P3/P6; D's bespoke `polyUnaryTM`). Under the fills'
  **no-touch rule** (cite or ignore, never remove/modify) they remain in
  the files, admission-free but partially dead. Maintainer position:
  serial post-gate dedup under E5, with D7's split discipline
  (byte-identical relocation, ordered-sequence comparison, ride-along
  audit). Review the deferral; flag any superseded helper that is
  actually *consumed* by a final proof in a way that smuggles an
  unaudited route.
* **D7 extension — the ClassNP size exceptions.** EXP 2,887,
  Nondeterminism 2,627, TMSAT 1,908. Maintainer position: fold their
  splits into the already-approved trailing D7 queue
  (`Loop`/`Primitives`), same discipline, after this gate. Review
  whether anything forces a split before the E3 fills consume these
  files.
* **D6 (unchanged, for the record):** the two library shared-lemma
  promotions remain queued post-gate; no epoch-2 fill depends on them.

## What is under audit, and priorities

The eleven proofs and 386 private helpers, against the frozen
statements, the phase-gate invariant tables (in the attached briefs,
verbatim), the audited library contracts they consume, and the agent
reports (attached; challenge any attestation of theirs the maintainer
layer above does not independently cover). Priorities, riskiest first:

1. **The B2 reverse host** (`b2*`, 42 privates closing
   `NP_subset_iUnion_NTIME`). The five-step contract end to end: the
   **read-normalization seam** (`b2UnaryTM` changes only input reads;
   `b2_unary_run`'s exact-lockstep claim at every elapsed time;
   `b2_unary_first`'s transfer of the unary generator's first halt to
   arbitrary same-length inputs — this replaced the explicitly-missing
   scheduler relocation, so re-derive it, don't trust it); dispatch on
   the scheduler's **actual first halt**, never an upper bound as a
   clock; `b2_tables_coincide` as a definitional fact of the
   construction; all-branch totality with a **common** bound while
   actual per-branch halting times vary; the `C = 0`, degree-zero, and
   empty-input edges; the exact ledger `H(n) = 3n + Q(n) + τ(n) +
   A(n+Q(n)+1)^d + 5` and the `(B+A+5)·m^r` envelope feeding
   `cont_guess_normalize`'s frozen coefficient `K(C+1)^r·2^(r·max 1 c)`.
2. **The banked reverse assets** (B-cont, 36 privates): `contGuessTM`
   on the library's `captureAction`; coverage at **actual physical
   write positions** (`contSelect`/`cont_select_surjective`/
   `cont_guess_coverage`, zero-coefficient case included — never "the
   first Q(n) choices"); `cont_guess_time_bound`'s exact coefficient;
   `cont_guess_normalize`'s all-branch-halting route through
   `acceptsWithin_iff_of_halts` with both padding and backward
   truncation.
3. **The forward compiler** (`ntime_poly_subset_NP`): the phase-2
   invariant tables discharged in full; `cont_split_bridge :
   solveSplit C c = certificateSplit C c` proved by `rfl` — including
   the agent's recorded determination that the campaign's coefficient
   shift belongs to `NP.lean`'s padding convention, not this file; the
   `(A+13)(m+1)^(c+2)` envelope; the note-3 rule (no untimed
   composition, no bare computability substitution) everywhere.
4. **The enumerator discharge** (A-cont, 95 privates):
   `enumMachine_contracts` as an `exists_loopCfgTM` instantiation —
   §9b instance data (exact-width invariant, `incFixed`-getD-stall
   step, `R = 2^w − 1`, fuel `replicate w true` via the
   `Nat.bits (2^w − 1)` induction); the stall bridge to the
   checkpoint's rank enumeration; the configuration-export translation
   (round-3 item 5) — and the fact that **three targets funnel through
   this one private**, so an error here fells the A/C cluster.
5. **The TMSAT budget chain** (D, 87 privates): D-MEM's quadruple
   parser under the exact-value discipline; the clock conversion
   (`pairMapSnd` + `lengthBits`); the odd split at `(1,1)`; D-WRAP as
   `pairValid` + `pairConcat` + capture; D-EMIT's §9c pairing recipe
   over exact unary runs with the explicit `T'` deadline formula
   (never majorizing the certificate length); the bridge consumed
   through its public statement only.
6. **Exercise 2.1** (C, 54 privates incl. the HALT pair's 16 in
   `Reductions.lean`): both P8 orientations through the §9c recipe;
   the mandated **P10 at `(C+1, c)` / P8 at `(C, c)`** coefficient
   shift; the original-bound-test rule; the HALT pair's reduction
   plumbing against the frozen `Reductions.lean` vocabulary.
7. **Checkpoint strata and hygiene** (147 checkpoint privates): the
   superseded families are admission-free and untouched per the
   no-touch rule — verify no final proof silently routes through a
   superseded helper whose own contract was never finished; privates
   match their stated contracts; nothing public-worthy smuggled
   private beyond the recorded D6 requests; library contracts consumed
   at their audited statements (C's fourteen, A's catalog instances,
   B's `captureAction`/`splitSolve`, D's primitive rows); the
   deliveries' own kernel-traversal claims spot-checked against the
   attached program and logs.

Severity scheme as always: blocker / major / minor / note; findings to
`audits/ch2-epoch2-findings.md`; this pack is immutable once sent
(errata via the resolutions file).

## Verification appendix (runs and manifest)

* Integration sweeps (fresh-olean, zero errors): 53/53 at 29 admissions
  (checkpoints), 57/57 at 23 (continuations), 57/57 at **21** (B2;
  attached). Logs: `audits/logs/ch2-e2-checkpoint-*`,
  `ch2-e2cont-{sweep,axioms,lint}.log`, `ch2-e2cont-B2-*` (committed;
  final three attached).
* Closure attestation: `ch2-e2cont-B2-axioms.log` (attached), from the
  attached committed program — exit 0, every expectation met.
* Lint: `ch2-e2cont-B2-lint.log` (attached): 0 FAIL / 3 WARN in scope,
  as itemized in attestation 5.
* Bundle manifest — **34 attachments** after the pack: the 5 owned
  sources (`EXP`, `Nondeterminism`, `NP`, `Reductions`, `TMSAT`); the
  4 model files (`TuringMachine/Nondeterministic`, `ClassNP/NTIME`,
  `ClassNP/PolyTime`, `ClassP/P`); the 9 briefs
  (`ch2-epoch2-batch{A,B,C,D}`, `ch2-e2cont-batch{A,B,C,D}`,
  `ch2-e2cont-batchB2`); the 10 agent documents (9 REPORTs + batch C's
  filed continuation plan); the closure program; the 3 final logs
  (sweep, axioms, lint); the span attestation; the 57-module order
  list. Total 5 + 4 + 9 + 10 + 1 + 3 + 1 + 1 = 34. The phase-1/2/3
  findings/resolutions, both library-gate records, the design document
  (§9b/§9c), and all earlier logs are committed in the repository at
  the paths the briefs and reports cite.
