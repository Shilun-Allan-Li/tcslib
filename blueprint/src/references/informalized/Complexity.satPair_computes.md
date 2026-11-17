<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPair_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time bound for the pairing machine

**Claim.** If $M$ computes $f(x)$ within $T(|x|)$ steps on every input, then the pairing machine computes $x\mapsto\langle f(x),x\rangle$ within $4T(n)+2n+8$ steps on inputs of length $n$.

**Proof.** Fix an input $x$. By the startup lemma (Complexity.satPair_start), after some $s\le T(|x|)+|x|+|f(x)|+5$ steps the pairing machine is in replay state with $f(x)$ captured and the output empty. The replay lemma (Complexity.satPair_replay), applied to the whole captured word, then takes $2|f(x)|+2$ steps and appends its doubled bits and the separator $01$. The copy lemma (Complexity.satPair_copy), applied to the whole input, takes $|x|+1$ further steps and appends $x$, halting with the desired encoded output. The run-composition law (Turing.MultiTapeTM.runFrom_add) combines these consecutive runs, and the characterization of computation by halting state and output (Turing.FinTM.computesInTime_iff) gives computation within the resulting time bound. Since output length is at most elapsed time (Turing.MultiTapeTM.output_length_le), the assumed computation of $f(x)$ implies $|f(x)|\le T(|x|)$. Substituting this and $|x|=n$ into the total time gives at most $2T(n)+2n+2T(n)+2+1+5=4T(n)+2n+8$. Monotonicity of computation time (Turing.FinTM.ComputesInTime.mono) extends the exhibited run to that bound.

**Key facts.** `Complexity.satPair_start`, `Complexity.satPair_replay`, `Complexity.satPair_copy`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.ComputesInTime.mono`.
