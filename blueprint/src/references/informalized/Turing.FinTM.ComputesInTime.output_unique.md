<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.FinTM.ComputesInTime.output_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of the Completed Output

**Claim.** If the machine computes $w$ from $x$ within $t$ steps and computes $w'$ from $x$ within $t'$ steps, then $w=w'$.

**Proof.** Extend both computations to the common time $\max(t,t')$. Monotonicity of computation in the time bound ensures that both still witness computations at that time (`ComputesInTime.mono`). At the common time, the deterministic run from the same initial configuration has a single output. The two computation witnesses identify that output with $w$ and with $w'$, respectively, so $w=w'$.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`.
