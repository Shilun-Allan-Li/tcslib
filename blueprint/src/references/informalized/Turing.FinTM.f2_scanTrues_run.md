<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_scanTrues_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning a True Prefix

**Claim.** If the first $j$ entries of the input are true and the machine's transition on true moves right, stays in state $q$, and emits false exactly when $e$ is true, then after $j$ steps it is at position $j$ in state $q$, with $j$ false outputs when $e$ is true and empty output otherwise.

**Proof.** Induct on $j$. At $j=0$, no step has occurred, so the initial scan configuration already has the asserted state, position, and empty output. For the induction step, the hypothesis that the first $j+1$ entries are true implies both that the first $j$ entries are true and that the bit at index $j$ is true. By induction, after $j$ steps the machine is in state $q$ at position $j$, with the prescribed output for those $j$ steps. The run-length recursion expresses the next run as one step after those $j$ steps (Turing.MultiTapeTM.runFrom_succ_eq_step'). The current bit is true, so the transition hypothesis applies: it stays in $q$, moves right, and emits false if $e$ is true, or nothing otherwise. The head advances to position $j+1$ by the right-move fact (Turing.moveInputPos_pos_of_ne_right). Appending this emission gives exactly the claimed output for $j+1$ steps; configuration extensionality for zero work tapes (Turing.Cfg.ext_zero_tapes) completes the comparison.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_scanCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
