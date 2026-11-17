<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.BPDecidesInTime.runsInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision Implies Bounded Halting

**Claim.** If $N$ satisfies the bounded-error decision condition within time $T$, then $N$ halts on every branch within $T(|x|)$ steps for every input $x$.

**Proof.** Fix an input $x$. The decision condition at $x$ is a conjunction whose first component says exactly that $N$ halts on every branch within $T(|x|)$ steps. Taking that component for each input gives the claimed time bound.
