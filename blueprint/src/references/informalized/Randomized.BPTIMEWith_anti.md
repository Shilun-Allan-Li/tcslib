<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPTIMEThreshold.lean :: Randomized.BPTIMEWith_anti -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in Acceptance Probability

**Claim.** If $\rho'\le\rho$, then every language decidable within the stated randomized time bound with acceptance probability at least $\rho$ on every input is also decidable within that bound with acceptance probability at least $\rho'$.

**Proof.** Unpack membership in the higher-threshold class to obtain a constant, a machine, and its time and probability guarantees. Keep the same constant and machine. The time bound is unchanged, while the probability guarantee weakens from $\rho$ to $\rho'$ by the assumed inequality. Monotonicity of the machine-level bounded-error condition applies these two pointwise comparisons (`Turing.FinNDTM.BPDecidesInTimeWith.mono`), giving the desired membership.

**Key facts.** `Turing.FinNDTM.BPDecidesInTimeWith.mono`.
