<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_parity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity step in multiplication

**Claim.** At a parity state with bit $b$, if $b$ agrees with the parity of register $11$, the program reaches the carry-halving state without changing registers; otherwise it halts with answer false.

**Proof.** The remainder of register $11$ upon division by $2$ is either $0$ or $1$. Split according to the proposed bit and these two possibilities. When they agree, the parity instruction selects the carry-halving state, leaving registers unchanged; a single-step reachability fact establishes the claim. When they disagree, it selects the answer-false state, and the return lemma gives a false halt; the halting-step principle includes the parity instruction in that run. The register bound is unchanged throughout.

**Key facts.** `Complexity.mult_preconditions`, `Complexity.LogProg.AReach.single`, `Complexity.mult_return`, `Complexity.LogProg.AHalt.step`.
