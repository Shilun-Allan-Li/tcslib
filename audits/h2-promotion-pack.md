# External audit pack — H2-S: promoting the step block to a public host (statement gate)

Campaign: Arora-Barak chapters 3-4, the host-first rule (`policy.md` §1, **Hosts come first**;
`machine-library-design.md` §14). B5a H1's continuation (fills-7) proved, privately in
`TuringMachine/CodeSimulator.lean`, **the complete generic step block**: one finite machine per
work-tape count `k` that simulates one transition of a `k`-tape coded table. That is host H2 of
the registry. Its named consumers are H1 itself (the uniform simulator), EXPCOM through H1, B6's
self-application universal `U₀` and `space_universal`'s `SU` (RD-3), C1 (the NTIME hierarchy) and
U-1 (re-deriving the chapter-1 universal machine). The rule says a host is promoted, by PR and gate,
before a second consumer is briefed (backlog F7-1(a)).

**This gate audits the proposed public statements and the promotion plan.** The proofs exist.
The maintainer's later PR (H2-M) moves them unchanged into a new public module, with its own
freeze check, replay and gate.

**The maintainer's proposal** (a sub-agent's design, reviewed by the maintainer):
- **promote as is, now:** move the proved declarations unchanged into `Build/StepBlock.lean`
  (namespace `Turing.StepBlock`), stated in the existing style, and have H1 cite them;
- **generalize later,** by separate theorems or host-side routes: an emission mode, a
  choice-bit-indexed table, a sharper time clause, and the MIG-0b round adapter.

**Bundle:** `audits/h2-promotion-bundle.md` holds:
- this pack, the standards, and the design note `audits/evidence/h2/H2-design.md` (consumers,
  recommendation, the module, the move, the gates, open questions O1–O12, sizes);
- the statement draft `audits/evidence/h2/StepBlockDraft.lean.txt`, with its elaboration and
  axiom log and its fidelity log and script;
- the move's dry run (`MoveProbe.lean.txt` and its output) and the C1 probe;
- the delivery report `audits/b5a-fill-agent-reports/h1-2-REPORT.md`;
- the source `CodeSimulator.lean`, and the consumers' files: `CounterLoop`, `VirtualInput`,
  `EXPCOM`, `Codes2Tape`, `NTimeHierarchy`, `NDCodes`, `Universal`, `UniversalInterpreter`, and
  the restated `Hierarchy` (`audits/evidence/b6-restatement/`);
- the design document and the backlog.

## What the draft states (verify)

`StepBlockDraft.lean` copies the definitions under public draft names in
`Turing.Draft.StepBlock`; the landed names drop `Draft.`. The rename map is in the design note's
Appendix A. It states seven contracts, sorried in the draft and proved in `CodeSimulator.lean`:
- **`roundTM_effect`, the main contract**, from the private `h1Round_effect`. Start at `entry`
  on a configuration representing (`Rep`) a live source configuration of the same input. The
  round then reaches, in some time `T` with `0 < T ≤ 50·(|table| + 1)`, either `entry` or
  `halt` (`halt` exactly when the source action halts). The endpoint represents the source's
  next configuration, and the summary cell is updated by `summaryEmit`. Strictly between `0`
  and `T` neither exit is visited, and nothing is emitted. Each mirrored and input head is at
  its start or its end position; each auxiliary head stays within the bound and returns to cell
  `0`.
- the whole-record skipper's contracts (`recordSkipTM_run`, `_spec`), the successor leaf's, and
  the fixed-field reader's (`recordTM_effect`).

**Five small additive results are proved in the draft:** `summaryEmit_none`, two visited-cell
lemmas, `roundTM_visited` and `roundTM_iterate`. They are what `U₀` and U-1 will cite.

**What the contract does not state:** a space clause (it follows from the envelope), an input
device other than the native one, a choice bit, emission (only the summary cell), an exact time
(the proof supports about `7·|table| + 3q + |word| + 42`), composition over rounds, or the
`Contract` form.

## Brief for the auditor

1. **Fidelity.** Check that every public statement and copied definition in the draft is the
   private one renamed: 58 of 58 per `fidelity.log`, with a two-mutation negative control.
   Rerun the attached `fidelity.py.txt` reasoning on the bundle's sources if you can. Check that
   the five additive results are stated and proved as claimed.
2. **"Promote as is."** For each consumer, check the design note §2's verdict against the
   consumer's files:
   - H1: the round hypotheses of `counterLoopTM_run_done`;
   - B6's `U₀` and `SU`: verbatim output by blanking the summary cell before each round and
     forwarding it after, since `summaryEmit none b = b`; the space ledger from the additive
     results; `SU`'s suffix input through H5;
   - C1: the probe's claim that the nondeterministic code's table is `tableBitsK` of a
     choice-lifted deterministic table on `2(n+1)` states, so that no choice-bit generalization
     is needed;
   - U-1: the stated per-round bound does not fit the frozen `universalBlockBound` (open question
     O8).

   Is any consumer's need understated? Should any generalization happen at promotion rather than
   later?
3. **The `Contract` question.** The design says MIG-0a's first-exit `Contract` does not fit,
   because `entry` is an exit at time `0` and the round has two exits; the step block is
   MIG-0b's return-or-escape round, with an adapter once that layer lands. Is this right? Is
   anything lost by stating it in the existing style now?
4. **The module and the move.** Check:
   - the home, the namespace and the three imports (`CodeFormat`, `Build.Seam`, `Build.Catalog`);
   - the roughly 70 public names (41 definitions, 6 instances, 23 theorems), and whether a
     narrower surface would be better (O5);
   - what leaves `CodeSimulator.lean`, with no private copy kept;
   - the dry run's claim: 121 declarations moved verbatim, 0 errors and 0 sorries, the same 67
     inherited linter warnings;
   - the 8-module replay closure.
5. **Timing (O2).** The move must land between the B5a continuations, since both own regions of
   `CodeSimulator.lean`, and two are in flight now. Is the proposed carve-out right?
6. **Open questions O1–O12** (design note §5): rule on any you disagree with.
7. **Documentation and policy:** docstrings, sketches, attribution and the 100-column limit.
8. Report anything else the draft or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Elaboration** (`audits/logs/h2-statements-elaboration.log`): the draft, read-only against the
  fills-7 snapshot, gives 0 errors, 7 sorry warnings (the seven contracts) and no other warnings;
  the axiom prints use at most the standard three. The maintainer re-ran the draft's
  elaboration independently: the same counts.
* **Fidelity** (`audits/evidence/h2/fidelity.log`): 58 of 58 copied declarations match after
  renaming, and the negative control is caught.
* **The move's dry run** (`MoveProbe.lean.txt`, `moveprobe.out.txt`): 0 errors, 0 sorries.
* **The C1 probe** (`C1LiftProbe.lean.txt`): elaborates with 0 errors and 0 warnings.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/h2-promotion-findings.md`. The gate closes when it has zero blockers and zero majors.
