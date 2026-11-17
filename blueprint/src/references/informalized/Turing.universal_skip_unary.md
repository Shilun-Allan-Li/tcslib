<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_skip_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Cost Unary Skip

**Claim.** Starting in the unary-skipping phase at the beginning of a field of $n$ ones followed by a zero, after $n+1$ steps the table cursor has advanced by $n+1$. If the remaining-record count is zero, the control enters the continuation for the destination; otherwise it enters fixed-field skipping with the count decreased by one and field index zero. The state tape and its cursor are unchanged.

**Proof.** Proceed by induction on $n$, allowing the prefix $l$ to vary. If $n=0$, the current table cell is the terminating zero, by the table-reading fact (`universal_table_read`). The machine therefore takes one step directly to the indicated continuation: with zero remaining records this is the destination continuation, and otherwise it is fixed-field skipping with the count reduced by one. The table cursor advances once, while the state tape and cursor do not change. For the inductive step, the current cell is one, again by `universal_table_read`. The transition stays in unary-skipping mode, advances the table cursor by one, and leaves the state tape untouched. Regard this first one as appended to the prefix, so the remaining table has $n$ ones followed by zero. The induction hypothesis now applies to that new prefix and proves the claimed final control and cursor after the remaining $n+1$ steps. Combining the initial step with those steps gives the stated total of $(n+1)+1$ for this inductive case, which is the required cost for $n+1$ ones.

**Key facts.** `Turing.universal_table_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.universalEval_step`.
