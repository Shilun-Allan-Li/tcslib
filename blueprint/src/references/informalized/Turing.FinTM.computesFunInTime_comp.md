<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.computesFunInTime_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time-Bounded Composition

**Claim.** If finite machines compute $f$ and $g$ within bounds $T_1$ and $T_2$, and $T_2$ is monotone, then a finite machine computes $g\circ f$ within a constant multiple of $T_1(n)+T_2(T_1(n))+1$.

**Proof.** Use the buffered composition machine, which first runs the machine for $f$ and then the machine for $g$ on the resulting word. On input $x$, the output-length bound for a run of $M_1$ shows that $|f(x)|\le T_1(|x|)$. Monotonicity therefore gives $T_2(|f(x)|)\le T_2(T_1(|x|))$. The buffered composition bound says that these two computations, including the buffering overhead, take $T_1(|x|)+|f(x)|+2+T_2(|f(x)|)$ steps. Applying the two inequalities bounds this by $2(T_1(|x|)+T_2(T_1(|x|))+1)$. The machine thus computes the composite within the stated bound with $c=2$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.FinTM.ComputesInTime.mono`.
