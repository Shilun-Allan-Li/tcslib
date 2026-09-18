# External audit pack — Fill campaign, Epoch 3 (third fill round)

Audits commit `b519a004` on `complexity/arora-barak-ch1`. Since the epoch-2
resolutions (`audits/epoch2-resolutions.md`), four things happened. **(a)**
The **epoch-3 merge refactor** (commit `71721842`, executing the epoch-2
audit's endorsed pre-work): new raw `TuringMachine/Sweep.lean` (the
one-work-tape construction's zipper/transduction layer promoted verbatim,
`Nodup` hypothesis preserved, plus initialized-run `source_bounds`),
`Turing.Action.apply_workTapes` promoted in `Simulation.lean` with
`AlphabetReduction` rewired to it, `SingleTape.lean` trimmed to 981 lines —
with a declaration-level check that no public name was lost. **(b)** A
**policy amendment** (commits `63ed999e`, `cead5966`): `policy.md` §2 now
mandates *statement prose* — every public declaration's docstring begins with
a natural-language statement of the result — with a mechanical presence check
added to `scripts/style_lint.py`; a campaign-wide survey found 2 deficient
declarations out of 176, both on **audited files** and both comment-only
fixes (`CodeTM.toFinTM_k` gained a docstring in `Encoding.lean`;
`HALT_eq_true_iff`'s bare label became a full statement in `Halting.lean`) —
flagged here for the freeze check. **(c)** The **epoch-3 fill round**: three
independent cloud agents (zip delivery), with batch B delivered as an honest
WIP and completed by a **continuation batch B2** in a fresh session from a
self-contained brief; the maintainer verified each delivery and integrated
six agent commits with authorship preserved. **(d)** Two **architectural
design questions were reserved for human review** (plan §5, "Open design
questions"): batch 3A's Mathlib-computability-bridge route and batch 3B's
universal-interpreter architecture. The auditor should *assess correctness*
of both constructions as usual, but their design disposition is explicitly a
human decision, out of this round's gate. Record findings in
`audits/epoch3-findings.md`.

The campaign standing: **20 of the 21 audited sorries are now proved.** The
one that remains is `timed_universal` (epoch 4). **[AB09, Theorem 1.9]
(untimed evaluator + quadratic corollary), [AB09, Theorem 1.10], and [AB09,
Theorem 1.11] are all fully machine-checked with no admissions.**

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Statement freeze / drift.** Over the whole fill span
   (`71721842 → b519a004`), exactly **four** `.lean` files changed:
   the three owned files plus `Halting.lean`. Comment-stripped,
   `Halting.lean` is **identical** (the statement-prose fix is comment-only);
   for the three owned files, a comment-stripped **multiset** comparison
   shows the only line removed anywhere is `sorry` — once per target (the
   line-diff shows 18 apparent removals in `Oblivious.lean`; all 17
   non-`sorry` lines reappear verbatim — diff re-anchoring across ~3,300
   insertions, verified by multiset). Public-declaration name diffs on all
   three files: **zero drift** (Encoding 12 public, Oblivious 2, Universal 3
   — unchanged; every fill declaration is private). The three public theorem
   headers in `Universal.lean` were additionally compared byte-for-byte
   against the pre-fill base: identical. The refactor span
   (`36641745 → 71721842`) had its own declaration-level check recorded at
   the time (plan decision log).
2. **Elaboration.** Full 25-module sweep via the strengthened
   `scripts/lean_check_tree.sh` (exit-status + fresh-olean enforcement),
   fresh olean tree, Lean 4.25.0 / mathlib `029db123ddaa`: **zero `error:`
   lines, zero gate failures**, exactly **one** `declaration uses 'sorry'`
   warning (`Universal.lean:2454`, `timed_universal`). Run on the combined
   integrated tree — which no agent lineage ever elaborated (A and C based
   on `71721842`; B2 continued B's branch without A/C).
3. **Axiom footprints** (`#print axioms`, maintainer-run on the integrated
   tree):

   ```text
   'Turing.universal'                            [propext, Classical.choice, Quot.sound]
   'Turing.universal_quadratic'                  [propext, Classical.choice, Quot.sound]
   'Turing.timed_universal'                      [propext, sorryAx, Classical.choice, Quot.sound]
   'Turing.exists_effectiveMachineCode'          [propext, Classical.choice, Quot.sound]
   'Complexity.oblivious_of_mem_DTIME'           [propext, Classical.choice, Quot.sound]
   'Complexity.UC_not_computable'                [propext, Classical.choice, Quot.sound]
   'Complexity.UC_computable_of_HALT_computable' [propext, Classical.choice, Quot.sound]
   'Complexity.HALT_not_computable'              [propext, Classical.choice, Quot.sound]
   ```

   The sole remaining `sorryAx` carrier is `timed_universal`.
4. **Soundness scan.** Across the entire fill span: no added `axiom`,
   `native_decide`, `implemented_by`, `@[extern]`, or `unsafe`; **no added
   `set_option` of any kind** (file headers unchanged); 4 structure-level
   `deriving Fintype/DecidableEq` uses and 14 kernel-checked `decide` calls.
   Import additions (programmatic inventory from the span diff):
   `Encoding.lean` + `Mathlib.Computability.TMToPartrec`,
   `Mathlib.Data.Fintype.Vector`; `Oblivious.lean` +
   `Mathlib.Data.Fintype.Pi`, `Mathlib.Data.Fintype.EquivFin`,
   `Mathlib.Tactic.DeriveFintype`, and the in-repo `Simulation`/`Sweep`;
   `Universal.lean` **none**. The `TMToPartrec` import is the 3A bridge
   (design question 1) — it pulls Mathlib's recursion-theory/TM2 development
   into the chapter's import cone; the fill's correctness then rests on
   Mathlib's proved `ToPartrec.Code.exists_code` and `PartrecToTM2.tr_eval`
   plus the batch's private `bridgeTM` simulation, all kernel-checked.
5. **Policy conformance** (`scripts/style_lint.py`, now including the
   statement-prose presence check from amendment (b)). Campaign tree: zero
   FAIL; **three** size WARNs, all escalated in the respective agent reports
   and accepted in the plan decision log pending the epoch-3→4 merge splits
   — `Encoding.lean` 2263 lines (bridge split due), `Oblivious.lean` 4086
   (decoration/coding layer split due), `Universal.lean` 2465 (shared
   promotion of the block-simulation layer due). Every sorry carries a
   sketch; facades import all children; legacy `NPReductions/*` FAILs remain
   out of scope (recorded separately).
6. **Delivery provenance.** Four zip deliveries per the standardized
   contents (report, sources, format-patch, git bundle, full sweep log,
   axiom log, SHA256 manifest). All manifests verified; bases verified as
   `71721842` (B2: continuation of `fill/epoch3-B` with the WIP commit
   `f191b918` as unchanged parent); flat sources, patches, and bundles
   mutually consistent (3A's flat file differed from the applied result by
   exactly the one `cead5966` docstring line its base predated); the agents'
   sweeps and axiom logs agree with the maintainer's independent runs on
   each lineage and on the combined tree. Reports preserved in
   `audits/epoch3-agent-reports/` (including the batch-B WIP report — its
   enumerated open obligation is what B2's brief and delivery closed).

## What was filled / new surface

| Batch | Now proved | New declarations | Notes |
|---|---|---|---|
| A (Encoding) | `exists_effectiveMachineCode` | 138 handwritten privates (+ derived instances; lint tallies 153) | **Deviation, flagged by the agent**: canonizer obtained by proving the parse-then-reserialize function primitive recursive and compiling through Mathlib (`ToPartrec.Code.exists_code` → `PartrecToTM2.tr_eval`), simulated in-model by a private 4-work-tape `bridgeTM`, landed in binary via the proved `alphabet_reduction`; time bound by finite maxima (no polynomial claim — permitted, `canonizerTime` is existential). Parser follows Argument A's grammar with an up-front `81·(numStates+1)` length guard |
| B + B2 (Universal) | `universal` | 104 privates (82 WIP + 22 continuation) | Prefix-only startup, canonizer capture onto a table tape, four-tape interpreter (fixed finite `UniversalControl`), virtual left boundary marker, unary state tape; per-phase **exact** ledger realized: `universalBlockBound = 3L + 5N + 20` unchanged from the WIP's proposal; forward `C·(t+1)` with `C = S + B`, converse covers divergent sources with no fairness assumption |
| C (Oblivious) | `oblivious_of_mem_DTIME` | 238 privates per the agent's inventory (lint's regex tallies 233) | Three layers: masked-clock capture + length-only schedule, decorated trajectory invariant, transverse parallel binary coding (one physical step per logical step); explicit constant `c = 18(a+1)² + 23(a+1) + 3b + 25`; oblivious on **all** inputs of each length including empty input and differing decision outcomes |

## Brief for the auditor

Ground rules as in all previous rounds (trusted surface; no blanket
approval; tactic scripts are Lean-checked and axiom-audited — out of scope).
Priorities:

1. **The 3A parser and bridge seam.** The decoder must implement Argument
   A's exact grammar (canonical state-count bits, bounded unary fields,
   fixed dictionaries, exact table size, all-true padding law, short-circuit
   on the first incomplete record, malformed ↦ canonical trivial machine).
   Then the two semantic joints of the compiler route: (i) does the
   primitive-recursiveness reduction really compute `(decode ·).serialize`
   on **every** `List Bool` (empty input, maximal padding, oversized
   declared tables)? (ii) does `bridgeTM`'s simulation of the TM2 stack
   machine — stacks as tapes, sentinel I/O coding — faithfully transport
   Mathlib's `tr_eval` semantics into our `ComputesInTime`, including the
   finite-max time-bound extraction and the final `alphabet_reduction`
   application? Confirm the deviation appendix is honest and no polynomial
   bound is claimed anywhere.
2. **The B2 live-step block.** Verify record selection against
   `CodeTM.serialize`'s enumeration order (state groups of nine records,
   input-major/work-minor read offsets): one erased unary state symbol per
   skipped group, `P = P_g + P_b` decomposition, eight fixed action bits +
   optional unary successor. Then checkpoint preservation in
   `universal_apply_record`: optional writes including blank, native
   emissions, clamped virtual input movement with the marker in lockstep
   (suppressed outward move at virtual zero), halting next-state fields, and
   the final-cursor bound that closes the `h ≤ L` invariant. Re-sum the
   realized ledger (`h + k + q₀ + 2q + P + 16` / `+ 2q′ + 19`) against
   `3L + 5N + 20`, and check the already-halted case's one-step absorbing
   transition. Confirm the converse (`universal_from_blocks`) genuinely
   covers divergent sources.
3. **The 3C schedule and coding layers.** Judge the construction against the
   phase-2 corrected oblivious design (phase-2 findings 1-2 and reaudit):
   length-only head trajectories at **every** physical time (not just
   macrostep boundaries), idle sweeps after early source halting, the
   masked-clock use of `TimeConstructible`, and the transverse binary coding
   preserving both obliviousness and the decision output. Re-sum the stage
   ledger to the explicit constant, with attention to the truncated
   subtraction in the input-reset stage and the `n ≤ U` uses.
4. **Freeze conformance of amendment (b).** Confirm the two statement-prose
   fixes on audited files are comment-only (attestation 1's
   `Halting.lean`/`Encoding.lean` claims), and spot-check the statement-prose
   quality of the *new* fills' public surface (there is none — all fill
   declarations are private; the check is that this is really so).
5. **The last sorry.** Confirm `timed_universal`'s statement and sketch
   remain implementable atop B2's infrastructure — in particular that the
   deadline-decorated interpreter it describes can reuse the capture
   wrapper, block-run assembly, and the exact ledger, and that the
   `pairEncode (pairEncode (Nat.bits t) α) x` layout matches the audited
   phase-3 conventions.
6. Assess attestations 1-6, including the drift-attestation methodology
   (comment-stripped multiset comparison) and the soundness-scan inventory.

## Specific questions

1. 3A: what does `decode` return on the empty string, and does
   `decode_encode_pad` hold with zero padding (`m = 0`) and for the
   canonical trivial machine's own serialization? Is the up-front length
   guard compatible with the padding law (a padded valid code is longer than
   the guard's minimum for its declared table)?
2. 3A: `bridgeTM` costs two native transitions per TM2 push and one
   otherwise — is the finite-max bound extraction per input length actually
   uniform over the *unbounded* value range of intermediate stack contents
   (i.e., why is the maximum finite)?
3. B2: `universal_skip_groups` erases one state-tape symbol per nine-record
   group. For the **last** state group (source state `q = numStates`) with
   maximal `P_b`, does the skip stay within the table (`h ≤ L` after the
   block), and does the selected record exist for every `(read, work)` pair
   including blank-blank?
4. B2: in the live-successor path, the copied unary successor can be
   `q′ = numStates` (maximal). Verify the `2q′ + 5` sub-ledger and the
   state-tape rewind cover it, and that a successor field of the *halting*
   form never leaves a stale partial copy on the state tape.
5. C: with `T n = 0` the hypotheses may be near-vacuous
   (`not_computesInTime_zero`) — confirm the theorem's content and the
   ledger survive `U = 0`, `n = 0`, and `a = 0` or `b = 0` degenerate
   multipliers.
6. C: obliviousness quantifies over **all** `t : ℕ`, beyond the simulator's
   halting time. Confirm the post-halting configurations keep both head
   positions length-determined (absorbing halt vs. continued idling — which
   is it, and is it proved for arbitrary `t`?).
7. Adversarial instantiations: `α = []` and `x = []` through `universal`
   (startup on an empty code; the canonizer output for `decode []`);
   a source machine halting at `t = 0` through the block assembly; the
   trivial machine through the whole 3A round-trip; a length-1 language
   through 3C with `T = fun _ => 1`.

## Scope

| Item | Where |
|---|---|
| Files under audit | `Encoding.lean` (fill + bridge), `Universal.lean` (fill), `Robustness/Oblivious.lean` (fill), `Halting.lean` (comment-only change), `Sweep.lean` (refactor surface, new since the last audited commit); all 25 modules attached |
| Source text | Arora & Barak 2009, §1.4 + Exercise 1.11 (representation; PDF pp. 45-46), §1.4.1 / Theorem 1.9 (universal machine; PDF pp. 46-48), Exercise 1.5 (obliviousness) |
| Context | `AroraBarakChapter1Plan.md` (incl. §5 "Open design questions" — reserved for human review), `policy.md` (amended §2), `audits/epoch2-{findings,resolutions}.md`, `audits/phase3-{findings,reaudit-findings}.md` (Arguments A-F: the canonizer contract and evaluator conventions), `audits/phase2-findings.md` (the corrected oblivious design), briefs `briefs/epoch3-batch{A,B,B2,C}.md`, agent reports `audits/epoch3-agent-reports/` |
| Out of scope | tactic proofs; statements confirmed in closed rounds beyond the freeze check; the *disposition* of the two human-reserved design questions (correctness of those constructions is in scope); legacy `NPReductions/*` style findings |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
