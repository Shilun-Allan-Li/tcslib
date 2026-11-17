<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.ComputableInTimeAndSpace.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of computability bounds

**Claim.** If a function is computable with given injective encodings within time bound $t$ and space bound $s$, and both bounds are pointwise at most $t'$ and $s'$, then it is computable with the same machine and encodings within bounds $t'$ and $s'$.

**Proof.** Unpack the computability witness: it supplies a finite state set, a machine, and a proof that this machine computes the function within the original bounds. Keep the same state set and machine. The function-computation monotonicity theorem (`ComputesFunInTimeAndSpace.mono`) transfers the computation to the larger time and space bounds, so these data witness the desired computability.

**Key facts.** `Turing.MultiTapeTM.ComputesFunInTimeAndSpace.mono`.
