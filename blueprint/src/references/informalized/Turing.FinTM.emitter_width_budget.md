<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitter_width_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Width Time Budget

**Claim.** Under the stated computation and monotonicity hypotheses, the machine computes the binary representation of $f(|s|)$ on $s$ within $T_E(|s|)$ steps; that representation has length at most this time, which is at most $T_E(|w|+1)$.

**Proof.** Apply the assumed computation property to the input $s$. This directly gives computation of the required binary representation within $T_E(|s|)$. The characterization of computation in time identifies that output with the machine's run output (`Turing.FinTM.computesInTime_iff`). A machine's output length after $t$ steps is at most $t$ (`Turing.MultiTapeTM.output_length_le`), so the representation has length at most $T_E(|s|)$. Finally, $|s|\le |w|+1$ and monotonicity of $T_E$ give $T_E(|s|)\le T_E(|w|+1)$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`.
