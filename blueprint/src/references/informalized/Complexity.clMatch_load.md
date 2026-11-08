<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_load -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loading a candidate row

**Claim.** For positive $l$ and words in the old and new rows of length at most $W$, the matcher loads the new row in at most $l(5W+7)+1$ steps, advances its stream cursor by the packed new row’s length, preserves its clock and flags, and enters the initial comparison control.

**Proof.** The bounded loading result for the loader machine (`Complexity.clLoad_first`), applied with both old- and new-row length bounds equal to $W$, loads the new row and advances the cursor by the length of its packed encoding. Its intermediate states avoid the loader’s terminal state. The loader placement simulation theorem (`Complexity.clPlaced_run`) therefore carries this run into the matcher, and the loading frame identity (`Complexity.clMatch_load_frame`) identifies the placed configurations with the stated matcher configurations, preserving the surrounding data. The loader bound simplifies from $l(2W+3W+7)$ to $l(5W+7)$. One additional matcher step, available because $l>0$ places the loader at its terminal control, enters the comparator’s initial control without changing the input-head position (`Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`). The successor identity for runs (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) incorporates this final step, giving the asserted bound and configuration.

**Key facts.** `Complexity.clLoad_first`, `Complexity.clPlaced_run`, `Complexity.clMatch_load_frame`, `Turing.FinTM.controlAction_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`.
