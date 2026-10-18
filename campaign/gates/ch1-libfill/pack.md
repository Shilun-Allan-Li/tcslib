# External audit pack — machine-construction library, fill audit

Audits the **proofs** of the machine-construction library: eight
Codex-authored fill commits across four batch rounds (W; P/P2/P3/P4;
L/L2) on the span `e346139c` → the pack commit, closing all 23 contracts
of `TCSlib/Complexity/TuringMachine/Build/` with ~250 new private
declarations. The **statements were audited separately and are not in
question here**: the spec surface closed a three-round adversarial gate
(`audits/ch1-infra-resolutions.md`, attached) — this round is the
companion proof audit, in the mold of the Chapter-2 epoch-1 fill audit:
proof correctness and helper hygiene against the frozen, audited
statements and their recorded construction ledgers. Gate closes on zero
blockers/majors. Record findings in `audits/ch1-libfill-findings.md`.

**Evidence separation.** Out of scope: the 28 Chapter-2 campaign
admissions (their own epoch gates); the bridge export and TMSAT
discharge (proof-audited at the infra round, blob-pinned unchanged); the
model files themselves (audited across the Chapter-1 campaign — they are
attached as the definitions the proofs elaborate against, not for
re-audit). The two delivery hosts' disclosed `/proc/<pid>/exe` shims are
superseded by the maintainer's independent fresh sweeps on an ordinary
host; the shims never entered the repository.

## Maintainer-side integration attestations (verify or challenge)

1. **Whole-span freeze.** Over the complete fill span, the net diff of
   `Build/` deletes **exactly the 23 audited contract `sorry`
   placeholders and nothing else** (the L checkpoint's intermediate
   admitted private was added and filled inside the span, so the net
   record is placeholder-exact), and adds **zero non-private
   declarations**. Public surfaces per file: 7/15/5/6 declarations,
   unchanged in order and content; all public docstrings byte-identical;
   module docstrings extended append-only. P4's kernel-export baseline
   independently confirms 78 public kernel declarations preserved.
2. **Per-delivery verification** (each recorded in the decision log at
   integration): checksums for all eight archives; per-patch
   deleted-lines audits; byte-identical replay in isolated worktrees
   before every `git am -3`; P3's and P4's attested integrated-source
   SHA-256 values reproduced. Disclosed-by-route imports only
   (P: three Mathlib modules, `ClassP.TimeConstructible`, `Composition`,
   `Wrappers`, `Loop`; L: `Wrappers`) — all order-legal, no cycles.
3. **Elaboration.** Four integrated-tree fresh 57-module sweeps, zero
   `error:` lines, admission counts stepping 33 → 30 → 29 → **28**
   (campaign-only; zero in `Build/`). The final sweep and closure
   attestation logs are attached (`ch1-libfill4-{sweep,axioms}.log`);
   earlier-round logs are committed under `audits/logs/ch1-libfill*`.
4. **Axioms.** The closure attestation (the attached, committed program
   `audits/programs/ch1-libfill-ClosureAxioms.lean`): all 23 contracts
   print at most the standard triple with **empty admission-root sets**;
   the headline and campaign regression roots unchanged. P4's own
   whole-`Build` kernel traversal covers 1,171 checked declarations with
   zero roots and no nonstandard axiom.
5. **Policy.** Combined lint (`ch1-libfill-lint.log`): **0 FAIL, 9
   WARN** — the seven pre-recorded size escalations plus the two
   fill-grown Build files, `Primitives.lean` (4,418 lines) and
   `Loop.lean` (2,693), whose exceptions were recorded with
   justifications at each integration. Every remaining `sorry`-free file
   keeps sketch-bearing docstrings; attributions intact.
6. **Deviations on record** (all cosmetic, all noted at integration):
   P3 worked under the campaign branch name locally (the epoch-1 D2
   precedent; zip delivery); L2's archive wrapped a top-level directory
   (corrected from P3 onward); both hosts' cache-setup failures were
   recovered without touching pins (their logs shipped in the archives).

## Dispositions requested

* **D6 — W's shared-lemma promotion requests.** Batch W requests serial
  promotion of `timed_input_bound` (a run's input position is at most
  its initial position plus elapsed steps) to the run calculus and
  `timed_rewind` (rewind from any input position in `pos + 2` steps,
  preserving work and output) to `Simulation.lean`; both are generic in
  tape count and state type. Maintainer position: **defer to a serial
  maintainer merge after this gate** (the D3 pattern) — the private
  copies compile standalone and three later fills already adapted the
  rewind pattern privately, so promotion is a dedup, not a blocker.
  Review the deferral and the two statements' promotion-worthiness.
* **D7 — the size exceptions.** `Wrappers.lean` 687 (within target);
  `Loop.lean` 2,693 and `Primitives.lean` 4,418, both justified at
  integration by exclusive-ownership fill rules concentrating every
  controller and invariant family in-file. Maintainer position: a
  **post-gate serial split** of the two large files (e.g. machines/
  invariants per family) is the natural follow-up, executed under the
  epoch-3→4 merge-refactor discipline (byte-identical relocation,
  ordered-sequence comparison) and ride-along audited. Review whether
  to require it before the E2 continuations consume the library, or
  allow it to trail.

## What is under audit, and priorities

The 23 proofs and ~250 private helpers, against the frozen statements,
the audited construction ledgers (the round-3 item-4 loop ledger; the
§9b instantiation tables; the frontier documents' interface
descriptions), and the agent reports (attached; challenge any
attestation of theirs the maintainer layer above does not independently
cover). Priorities, riskiest first:

1. **The loop host assembly** (L2: `loopHost_contracts` and its forty
   phase lemmas). Re-derive the checked time ledger (startup
   `≤ 9(T+1)`; segment `≤ 10(T+1)`; exported constant 10) against the
   audit's own round-3 ledger; check the phase-boundary seams (fuel
   capture → counter copy → synchronized rewinds → body release), the
   free-initial-entry discipline at zero fuel, the `findMode` dual
   output sharing one controller, the unreachable-terminal cases, and
   that the per-segment counter estimate is genuinely worst-case width
   (R3-2), not amortized.
2. **`capture_run`** (W): the induction every later fill instantiates.
   The halting-transition emission, the `bufferTape_append` head
   arithmetic, the liveness guard's exact role, preservation of
   arbitrary prefixes and host output.
3. **The split-search body** (P4): the `splitSafe` trace-composition
   family (the global positive-duration/anchor-exclusion argument — the
   known composition trap); the accepting emitter's native-bit claim
   (candidate used only as a length counter); the envelope
   `A = (C+1+5e)·2^e + 40` and the `s+1 ≤ 2(w+1)` step; the
   one-past-end silent stall preserving arbitrary bits; both exponent
   cases including `catalogPrefixTM` at `e = 0`.
4. **The conditional and the threaded map** (W4, P14): the
   multiplier-5 ledger (`2T₀ + 5` prefix; the input-position-≤-run-time
   rewind argument) and the coefficient-40 ledger — in particular that
   neither evaluates a time function at an inflated composition bound
   (the recorded trap).
5. **Harvest fidelity**: `catalogPolyUnaryTM` against the TMSAT source
   generator with the `e − 1` indexing (round-1 finding 5);
   `incFixedTM`'s detect-then-emit redesign against `enumCarry*`
   semantics; `lengthBits`' discharge by the public
   `Complexity.timeConstructible_id` — verify that theorem's witness
   really is a `Nat.bits ∘ length` machine at the required bound
   (`ClassP/TimeConstructible.lean` attached).
6. **The parser/threaded family** (P5–P13): the shared `pairExtractTM`
   invariants serving three contracts; `pairLenCheck`'s captured
   countdown; `stripLast`'s whole-encoding buffering against the
   audited marker discipline; buffer-before-emit discharged at every
   claimed point.
7. **Helper hygiene**: privates match their stated contracts; nothing
   public-worthy is smuggled private without a flag beyond the two D6
   requests; no helper restates an audited statement in disguise; the
   deliveries' kernel-traversal claims (opaque values, constructor
   dependencies, explicit expectations) spot-checked against the
   attached programs.

Severity scheme as always: blocker / major / minor / note; findings to
`audits/ch1-libfill-findings.md`; this pack is immutable once sent.

## Verification appendix (runs and manifest)

* Integration sweeps (all fresh-olean, 57/57, zero errors): 33
  admissions at the W+P+L checkpoint, 30 after P2+L2, 29 after P3, 28
  after P4 (`audits/logs/ch1-libfill{,2,3,4}-sweep.log`; the last
  attached).
* Closure attestation: `ch1-libfill4-axioms.log` (attached), from the
  attached committed program — exit 0, every expectation empty.
* Lint: `ch1-libfill-lint.log` (attached): 0 FAIL, 9 WARN as itemized
  in attestation 5.
* Bundle manifest — **32 attachments** after the pack: the 4 `Build/`
  sources; the 6 model/gadget modules (`Configuration`, `Deterministic`,
  `Finite`, `Simulation`, `Sweep`, `Composition`); `Encoding.lean` and
  `ClassP/TimeConstructible.lean`; the 3 harvest-source files
  (`ClassNP/TMSAT.lean`, `ClassNP/EXP.lean`, `ClassNP/Reductions.lean`);
  the design document; the infra-gate resolutions; the 10 agent
  documents (W, P, P2 + its frontier, P3 + its frontier, P4, L + its
  continuation, L2); the closure program; the 3 logs (final sweep,
  closure axioms, lint); the 57-module order list.
  Total 4 + 6 + 2 + 3 + 1 + 1 + 10 + 1 + 3 + 1 = 32. The six fill
  briefs and all earlier logs are committed in the repository at the
  paths the reports cite.
