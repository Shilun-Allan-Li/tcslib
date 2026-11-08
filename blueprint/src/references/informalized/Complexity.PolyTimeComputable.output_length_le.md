<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTime.lean :: Complexity.PolyTimeComputable.output_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial output-length bound

**Claim.** For every polynomial-time computable function $f$ on bit strings, there are natural numbers $C,c$ such that every input $x$ satisfies $|f(x)|\le C(|x|+1)^c$.

**Proof.** Unpack polynomial-time computability to obtain a machine computing $f$ within $C(|x|+1)^c$ steps on each input $x$. The machine's output after $t$ steps has length at most $t$ (`Turing.MultiTapeTM.output_length_le`), since each step can append at most one output symbol. The characterization of computation at a specified time (`Turing.FinTM.computesInTime_iff`) identifies that machine's output at the stated time with $f(x)$. Combining these facts gives $|f(x)|\le C(|x|+1)^c$ for every $x$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`.
