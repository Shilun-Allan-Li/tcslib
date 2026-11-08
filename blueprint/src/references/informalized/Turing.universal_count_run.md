<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_count_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Cost of Parsing a Count Field

**Claim.** For the stated doubled-field table, exactly $2|\beta|+2$ interpreter steps move from the count-first state to the initial-state copier when the flag is true, or to the initial-state skipper carrying $i$ otherwise, with the table head advanced by that same amount and the other configuration data unchanged.

**Proof.** Induct on the bit string $\beta$, keeping the prefix $l$ general. If $\beta$ is empty, the next two table cells are the delimiter $0,1$. The table-reading lemma identifies those cells (`universal_table_read`). The first interpreter step reads the $0$ and moves from the first-counting state to the second-counting state; the second reads the $1$ and enters the copier or skipper according to the flag. Both steps move the table head right once, so the final cursor is $|l|+2$, as required. For a nonempty string $b::\beta$, its first bit occurs twice consecutively in the doubled encoding. By the same table-reading fact, the interpreter reads $b$ at both positions: it alternates from count-first to count-second and back to count-first, advancing the cursor by two while leaving the state tape and its head unchanged. The remaining table is the doubled encoding of $\beta$ with prefix $l++[b,b]$. Apply the induction hypothesis to that suffix. The run-composition law concatenates these two initial steps with the remaining run (`runFrom_add`), giving total length $2+ (2|\beta|+2)=2|b::\beta|+2$ and final cursor $|l|+2|b::\beta|+2$. The one-step run law and zero-step run law justify the two-step base case (`runFrom_succ_eq_step'`, `runFrom_zero`); the interpreter-step description identifies each transition and updates the cursors (`universalEval_step`).

**Key facts.** `Turing.universal_table_read`, `Turing.universalEval_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_add`.
