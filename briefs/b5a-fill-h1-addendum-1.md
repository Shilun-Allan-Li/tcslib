# Addendum 1 to `briefs/b5a-fill-h1.md` (B5a, H1): a head envelope for the step block

Issued 2026-10-12, after dispatch. It adds one obligation to the step block. Your target,
by-declaration ownership, statement freeze, ancestor, verification and delivery are unchanged.
Record in `REPORT.md` that you received this addendum, and at which point of your work.

**Why.** The user has adopted a **host-first rule**: reusable control structures are built
generic and are never built as one-offs. Your brief already makes the step block the reusable
piece. Its next consumers include the space hierarchy (B6), which runs a universal machine
inside a space window. That needs a **space** guarantee from the step block, and your brief asks
only for a time bound. Proving the space guarantee now, while you prove the trace, is cheap.
Adding it after promotion would mean reopening the proof.

**What changes (binding):**
1. **Head envelope per round.** In addition to the silent relation-level trace and the per-round
   time bound `B·(|table| + 1)`, prove a head-envelope clause in the library's form (as in
   `exists_recordStepTM`, `Build/CfgRecord.lean`):
   `∀ u ≤ t, ∀ j, |pos_j(u) − pos_j(0)| ≤ ...`, with the following bounds.
   - **Mirrored tapes and the simulated input head.** Each of the `k` mirrored work tapes, and
     the head that carries the simulated input position, moves only as the corresponding
     simulated head moves. Throughout the round it stays between its round-start and round-end
     positions, which differ by at most one cell, and those positions track the simulated head
     exactly.
   - **Every other real tape** (table, state, scratch) stays within `B·(|table| + 1)` cells of
     where it started the round, and returns to its home at the round's end, where your trace
     already says so.

   Together these give the uniform-simulator space ledger: the simulated machine's space plus
   `O(|table| + 1)` per auxiliary tape. Do not prove that ledger itself. Prove only the per-round
   clause, as part of (or next to) the step block's contract.
2. **Self-contained contract.** The step block's main private theorem states the clause in its
   docstring statement, and is flagged "**promotion candidate (host H2, step block;
   `machine-library-design.md` §14)**".
3. **`REPORT.md`.** Under promotion candidates, give the step block's full contract verbatim,
   including the new clause.

**Non-binding, but helpful.** Keep the step block's input access in one place: the one sub-step
that reads the simulated input cell and moves the simulated input head. A later input-device
interface can then replace it. Avoid assumptions that would block a table indexed by an extra
choice bit, which the NTIME hierarchy needs later. Do not build either generalization.

**Priority.** `exists_uniformSimulator` comes first. If the clause would materially enlarge the
work (more than about a fifth), finish H1, then prove the clause as a separate private lemma
about the same step block. If you run out of budget, report the clause's frontier.
