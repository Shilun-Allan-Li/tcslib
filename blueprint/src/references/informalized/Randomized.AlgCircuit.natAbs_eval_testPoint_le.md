<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.AlgCircuit.natAbs_eval_testPoint_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Evaluation Bound at Test Points

**Claim.** For a finite arithmetic circuit $C$ and any Boolean string $u$, the absolute value of the circuit output at the specified block-based test point is at most $2^{5(|C|+12)2^{|C|+12}}$.

**Proof.** Each block of $|C|+4$ bits has value less than $2^{|C|+4}$, so after adding one every test-point coordinate has absolute value at most $2^{|C|+4}$. The circuit bound on evaluation over inputs of absolute value at most $X$ gives $|C(x)|\le X^{2^{|C|}}$ when $X\ge2$ (the evaluation-growth bound, `Randomized.AlgCircuit.abs_eval_le_pow`). Taking $X=2^{|C|+4}$ yields an output bound of $2^{(|C|+4)2^{|C|}}$. Finally, since $|C|+4\le5(|C|+12)$ and $2^{|C|}\le2^{|C|+12}$, this is at most the claimed, looser bound. The block-value estimate used here is `Randomized.blockVal_lt`.

**Key facts.** `Randomized.blockVal_lt`, `Randomized.AlgCircuit.abs_eval_le_pow`.
