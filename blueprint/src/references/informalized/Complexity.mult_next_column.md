<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_next_column -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advance to the next column

**Claim.** From the carry-halving state, under the stated bounds and position hypotheses, the program reaches the column state with register $11$ halved, register $7$ increased by one, and register $12$ replaced by $\min(v(12)+1,v(1))$, preserving all other registers and the required conditions.

**Proof.** First halve register $11$, then increment register $7$. The register-update bound lemma preserves the bound after each update, using the hypotheses that division does not increase the register and that the incremented value of register $7$ is within the bound. At the next result-test state, the program compares registers $12$ and $1$. If they agree, it returns to the column state without changing the current assignment; the position hypothesis makes the stated minimum equal to their common value. If they differ, the hypothesis $v(12)\le v(1)$ implies $v(12)<v(1)$, so the program increments register $12$ and returns to the column state. The minimum in this case is $v(12)+1$, and the position hypothesis ensures this increment stays within the bound. Reachability reflexivity handles the equal case; in the unequal case, one single-step reachability fact handles the increment. Prepending the carry-halving and next-column instructions gives the full run.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`, `Complexity.mult_preconditions`.
