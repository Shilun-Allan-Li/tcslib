<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.bufferedCompTM_computesFunInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running Time of Buffered Composition

**Claim.** If $M_1$ computes $f$ in time $T_1$, $M_2$ computes $g$ in time $T_2$, and $T_2$ is monotone, then the buffered sequential composition computes $g\circ f$ in time $n\mapsto 2\bigl(T_1(n)+T_2(T_1(n))+1\bigr)$.

**Proof.** Fix an input word $x$. Since $M_1$ computes $f(x)$ in $T_1(|x|)$ steps, its output length is at most that number of steps, by the general bound that a machine can output at most one symbol per step (`Turing.MultiTapeTM.output_length_le`). Hence $|f(x)|\le T_1(|x|)$, and monotonicity gives $T_2(|f(x)|)\le T_2(T_1(|x|))$. Buffered composition runs the first machine, transfers its output through the buffer, and then runs the second machine. The buffered composition time bound (`Turing.FinTM.bufferedCompTM_computesInTime`) therefore gives a run computing $g(f(x))$ in $T_1(|x|)+|f(x)|+2+T_2(|f(x)|)$ steps. The preceding inequalities show this is at most $2(T_1(|x|)+T_2(T_1(|x|))+1)$. A computation valid at one time remains valid at any larger time (`Turing.FinTM.ComputesInTime.mono`), so the composition computes the required output within the stated bound. The equivalence between computation and a halted run with the specified output (`Turing.FinTM.computesInTime_iff`) supplies the halted-run and output information used to obtain the output-length estimate.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.FinTM.ComputesInTime.mono`.
