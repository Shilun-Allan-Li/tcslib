<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.exists_comp_on_image -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition on the Image

**Claim.** If $M$ computes $f$ within $T_1(|x|)$ steps and $U$, on input $f(x)$, computes $g(x)$ within $T_2(|x|)$ steps, then a finite Boolean machine computes $g$ on each input $x$ within $2T_1(|x|)+T_2(|x|)+2$ steps.

**Proof.** Take the buffered composition of $M$ and $U$. Its composition theorem gives a run on $x$ producing $g(x)$ in $T_1(|x|)+|f(x)|+2+T_2(|x|)$ steps (`Turing.FinTM.bufferedCompTM_computesInTime`). The output of $M$ has length at most its running time, so $|f(x)|\le T_1(|x|)$: identify the computed output using the computation characterization (`Turing.FinTM.computesInTime_iff`), then apply the bound that output length is at most elapsed time (`Turing.MultiTapeTM.output_length_le`). Thus the composition runs within $2T_1(|x|)+T_2(|x|)+2$. Monotonicity of computation time extends the computation to that bound (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.ComputesInTime.mono`.
