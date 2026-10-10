# External audit pack — §12.6 framed catalog contracts (statement gate)

**Surface under audit:** five new sorried theorem statements in
`TCSlib/Complexity/TuringMachine/Build/Catalog.lean`, in the section "Framed
contracts (design §12.6)" just after the R3 rows:
`transferTM_run_ofCfg`, `copyTM_run_ofCfg`, `clearTM_run_ofCfg`,
`incrementTM_run_succ_ofCfg`, `incrementTM_run_overflow_ofCfg`. No machine is
defined or changed; the five machines (`transferTM`, `copyTM`, `clearTM`,
`incrementTM`, and their phase types) are the gate-closed §12 R3 definitions.
Record findings in `audits/s12-framed-findings.md`. **The gate closes on zero
blockers and zero majors**, which commissions the fill batch.

## Why these exist

The zone shift machines (`Build/Zone.lean`, `exists_zoneShiftInTM` and
`exists_zoneShiftOutTM`) have exactly two tapes: the zoned data tape and a
scratch tape that starts and ends as the unary level word. Their staging,
cleanup and binary navigation counter all run at **displaced heads beside
unrelated data**. The R3 rows are stated only from `Cfg.ofWords`, with heads at
the origin and globally buffered tapes, so none of them applies there.

The fill agent for those rows (ZF-A2, `audits/zone-agent-reports/f1-A2-REPORT.md`,
attached) stopped on this gap rather than copying the catalog's private trace. It
supplied a kernel-checked boundary regression: a bare transfer from a displaced
head on a valid carrier erases a cell belonging to the next zone. It also
supplied the typechecked type of the transfer contract it needed. Both are
attached. The statement under audit is that type, re-expressed in place, plus
the four siblings the same consumer needs. The design rationale is
`machine-library-design.md` §12.6 (attached).

## The common shape (verify for each)

Each contract quantifies over an **arbitrary** configuration `d` in the
routine's start phase. Its only hypothesis about the tapes is about the touched
word: for every relative offset `p` with `-1 ≤ p ≤ |w|`, the cell at
`pos + p` equals `bufferTape w p`. That is, the word sits at the head, with a
blank on each side. It then asserts three things.

1. **The exact configuration at the exact time** (`2|w| + 2`; for a successful
   increment, `2p + 2` where `p = (w.takeWhile id).length`). It is `d`
   with the state moved to the exit anchor and the word intervals rewritten.
   Every other cell, both head positions, the native input position and the
   output are unchanged.
2. **No earlier visit** to the exit anchor.
3. **Trajectory**: up to the exit, each touched head stays in
   `[pos − 1, pos + |w|]` (for a successful increment, `[pos − 1, pos + p]`),
   and every other head is fixed.

## Specific questions

1. **Truth at every boundary.** Check each statement at `w = []`; at an
   increment with `p = 0` and with `p = |w| − 1`; at overflow with `w = []`
   and `w` all `true`; and at heads displaced to negative coordinates.
   Previous gates in this campaign were lost on exactly such side conditions,
   so attempt at least three adversarial instantiations per statement.
2. **Hypotheses: necessary and sufficient.** Is the left delimiter at `-1`
   needed in each case? The return pass reads leftward until a blank. Is the
   right delimiter at `|w|` needed in each case? For a successful increment it
   is never read; requiring it is deliberately stronger, and consumers
   delimit anyway. Say whether this costs any consumer anything. Is anything
   assumed about the **destination** of transfer and copy? It should not be,
   since neither machine branches on the destination read. Check this against
   the transition tables.
3. **The finish configurations.** Are the rewritten intervals exactly right?
   For example, the transfer's destination interval holds
   `bufferTape w (q − pos_dst)` on `[pos_dst, pos_dst + |w|)`, and its
   delimiter cells are visited but never written. Does `incFixed` preserve
   width, so that the successful increment's interval `[pos, pos + |w|)`
   holding `v` is consistent?
4. **Specialization.** Does each framed contract imply its canonical R3 row
   (`transferTM_run`, `copyTM_run`, `clearTM_run`, `incrementTM_run_succ`,
   `incrementTM_run_overflow`) at `d := Cfg.ofWords …`? The fill brief will
   require the canonical rows to be re-derived from the framed ones, so this
   must hold.
5. **Fitness for the consumer.** Read the zone row statements in the attached
   `Build/Zone.lean`. Can a two-tape controller establish the delimited
   hypothesis, by saving the boundary cells in finite control, installing
   blanks, running the routine, and restoring them? And does the
   carry-sensitive `2p + 2` suffice for the audited geometric navigation
   ledger, `Σ_{r=1}^{2^i}(1 + v₂(r)) < 2^(i+1)`? Name any missing contract.

## Repository-side attestations (verify or challenge)

- **Elaboration.** `Build/Catalog` elaborates via `scripts/lean_check_tree.sh`,
  with exactly the five new `sorry` warnings. Everything downstream of
  Catalog replays with zero errors. Lint reports 0 FAIL.
- **Executed check.** The attached `audits/evidence/s12-framed/` harness
  evaluates the actual machines on concrete configurations with displaced
  heads, a nonblank outer frame and the boundary words. It compares the exact
  final configuration (both tapes over 30 cells, heads, input position and
  output), the no-earlier-exit clause and the trajectory bounds against each
  statement: 63 cases, all pass. A wrong-time negative control fails. This is
  evidence, not proof.

## Brief for the auditor

Audit the five statements, not tactic scripts. Hunt infidelity, vacuity, and
missing or excess hypotheses. Blind-restate each statement before reading its
docstring. Report in the standard findings table (blocker / major / minor /
note). Justify an empty table with your restatements and adversarial
instantiations.
