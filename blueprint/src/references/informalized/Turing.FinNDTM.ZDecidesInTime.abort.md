<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.ZDecidesInTime.abort -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting and success at twice the budget

**Claim.** For each input, every halting run gives the correct one-symbol indicator, and a uniformly chosen choice word of length $2T(|x|)$ yields a halting run with that output with probability at least $1/2$.

**Proof.** Fix an input $x$. The time bound $T(|x|)$ is at least $1$, by the lower bound built into the total nonhalting probability hypothesis. Apply the finite-horizon truncation estimate at $t=2T(|x|)$, which is positive. It gives the correct-output assertion for every halting run and bounds the success probability below by $1-T(|x|)/(2T(|x|))$. This expression is exactly $1/2$, proving the desired probability bound.

**Key facts.** `Turing.FinNDTM.ExpTimeLe.one_le`, `Turing.FinNDTM.ZDecidesInTime.truncate`.
