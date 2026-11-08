<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.abs_run_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Magnitude bound for circuit runs

**Claim.** For inputs bounded in magnitude by $X\ge2$, every indexed value in the run of any gate list $G$ has magnitude at most $X^{2^{|G|}}$.

**Proof.** Proceed by induction on the gate list, appending one gate at a time, and set $B=X^{2^{|G|}}$ for the preceding list. The old run values are bounded by $B$ by induction, and $B\ge X\ge2$. Appending a gate leaves every earlier indexed value unchanged; the only new value is the evaluation of the appended gate. An input gate has magnitude at most $X\le B^2$, and the constant gate has magnitude $1\le B^2$. For an addition or subtraction gate, the triangle inequality bounds its magnitude by the sum of two preceding magnitudes, at most $2B\le B^2$. For a multiplication gate, the product rule for absolute values bounds it by $B^2$. The new list has one more gate, and $X^{2^{|G|+1}}=B^2$, completing the induction. The decomposition of an indexed lookup in the appended run into either an old value or the new gate value is the list-indexing fact `Randomized.AlgCircuit.getD_append_singleton`; the description of the appended run itself is `Randomized.AlgCircuit.run_append_singleton`.

**Key facts.** `Randomized.AlgCircuit.run_append_singleton`, `Randomized.AlgCircuit.getD_append_singleton`.
