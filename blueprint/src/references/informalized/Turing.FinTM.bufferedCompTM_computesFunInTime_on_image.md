<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.bufferedCompTM_computesFunInTime_on_image -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition Time Bound on an Image

**Claim.** If $M$ computes $f$ in time $T_1$, and $U$ computes $g(x)$ from input $f(x)$ in $T_2(|x|)$ steps, then buffered composition computes $g$ in time $n\mapsto 2T_1(n)+T_2(n)+2$.

**Proof.** Fix an input $x$. The output-length bound for a machine run says that $|f(x)|\le T_1(|x|)$: apply the computation characterization to identify the output of $M$ at that time, then use the fact that at most one symbol is output per step (`Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`). The buffered composition time bound applied to the runs of $M$ on $x$ and $U$ on $f(x)$ gives a computation of $g(x)$ in $T_1(|x|)+|f(x)|+2+T_2(|f(x)|)$ steps (`Turing.FinTM.bufferedCompTM_computesInTime`). Using $|f(x)|\le T_1(|x|)$ and the hypothesis $T_2(|f(x)|)$ is the time allotted to $U$ on this input, this is at most $2T_1(|x|)+T_2(|x|)+2$. Monotonicity of computation time then gives computation at the stated bound (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.FinTM.ComputesInTime.mono`.
