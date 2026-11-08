<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.obliviousCandidate_decides -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness and time bound for the candidate

**Claim.** Under the clock-machine, growth, and decision-time hypotheses, the candidate decides $L$ within the stated quadratic time bound.

**Proof.** Fix an input $x$. The simulation result `dataTM_computes` gives a time at which the auxiliary data machine produces the encoded membership bit for $x$. The correctness of the parallel encoding (`parallelTM_computes`) transfers this computation to the candidate, so the candidate produces the indicator of whether $x$ belongs to $L$. Separately, `obliviousCandidate_halts` supplies a halting time $s$ no larger than the claimed bound. At time $s$ the candidate has halted; by the characterization of computation in a given time (`computesInTime_iff`), its output at that time witnesses a computation. The output uniqueness theorem (`ComputesInTime.output_unique`) identifies this output with the indicator already obtained from the correctness simulation. Finally, monotonicity of computation time (`ComputesInTime.mono`) extends this correct computation from $s$ to the claimed bound. Since $x$ was arbitrary, the candidate decides $L$ within that bound.

**Key facts.** `Complexity.dataTM_computes`, `Complexity.parallelTM_computes`, `Complexity.obliviousCandidate_halts`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Turing.FinTM.ComputesInTime.mono`.
