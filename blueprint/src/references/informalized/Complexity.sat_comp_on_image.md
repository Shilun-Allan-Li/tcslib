<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_comp_on_image -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition on the Image

**Claim.** If $M$ computes $f$ within $T_1(|x|)$ steps and $U$ computes $g(x)$ from $f(x)$ within $T_2(|x|)$ steps, then a finite machine computes $g$ within $2T_1(n)+T_2(n)+2$ steps on inputs of length $n$.

**Proof.** Apply the finite-machine composition theorem for computation on the image: first compute $f(x)$ with $M$, then run $U$ on that output, with the prescribed time overhead. The hypotheses here are exactly the first machine's time bound and the second machine's bound on inputs of the form $f(x)$, so the theorem supplies a finite machine computing $g$ with bound $2T_1(n)+T_2(n)+2$ ( `FinTM.exists_comp_on_image` ).

**Key facts.** `Turing.FinTM.exists_comp_on_image`.
