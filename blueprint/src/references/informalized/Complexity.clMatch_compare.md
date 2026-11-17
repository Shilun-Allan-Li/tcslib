<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_compare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded signed comparison

**Claim.** For distinct coordinates and words of length at most $W$, the matcher reaches the clock-test control in at most $2W+3$ steps, appending a bit that is true exactly when the positive row word plus the second target word equals the first target word plus the negative row word.

**Proof.** First, each of the four words selected for the comparator has length at most $W$. The comparator’s bounded-run result (`Complexity.clCmp_first`) supplies a time $t\le 2W+2$ and a verdict bit $b$. It proves that $b$ is true exactly when the sum of the values on comparator tapes 0 and 1 equals the sum on tapes 2 and 3, and that after $t$ steps the comparator is in its verdict state. By the definition of the four selected words, this equality is the desired equality between the positive row word and second target, and the first target and negative row word.

The comparison-slot frame identity (`Complexity.clMatch_cmp_frame`) identifies the matcher configuration with the embedded comparator’s starting configuration, and also identifies the embedded verdict configuration with the matcher configuration holding $b$. The comparator’s intermediate states satisfy the guard needed to simulate its run inside the matcher; the placement simulation theorem (`Complexity.clPlaced_run`) therefore lifts those $t$ steps to the matcher while preserving the surrounding tapes and heads. Finally, one more step commits the verdict bit and returns to the clock-test control. The run-length successor identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) expresses this final step, and the commit lemma (`Complexity.clMatch_commit`) gives the resulting clock and flag updates. Hence the total time is $t+1\le 2W+3$, with all other displayed data unchanged.

**Key facts.** `Complexity.clCmp_first`, `Complexity.clMatch_cmp_frame`, `Complexity.clPlaced_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.clMatch_commit`.
