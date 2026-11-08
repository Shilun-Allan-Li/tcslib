<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Count_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time computability of stored counts

**Claim.** If the unary word of length $t(z)$ is polynomial-time computable, then so is the unary word whose length is the stored movement count at time $t(z)$.

**Proof.** First construct the unary index $t(z)\,\mathrm{clRecFields}(M)+i$. The fixed multiplication of a polynomial-time unary output by the constant number of record fields is polynomial-time (\texttt{clA5Times_native}); appending the fixed unary word for $i$ preserves polynomial-time computability (\texttt{clNative_append} together with the constant-output result \texttt{clA5_pt_const}). This gives the index as a unary word. The header-field extraction result, composed with header-tail extraction, makes the trajectory field at that index polynomial-time computable (\texttt{clA5Field_native}, using \texttt{clHeaderField_native} and \texttt{clHeaderTail_native}). Finally, the stored count is the decoded field value capped by the stored horizon. Applying the polynomial-time capped-number result (\texttt{clA5SmallNum_native}) to this field and to the unary horizon, whose polynomial-time computability is supplied by \texttt{clA5Sizes_native}, yields the required unary output.

**Key facts.** `Complexity.clA5Times_native`, `Complexity.clA5_pt_const`, `Complexity.clNative_append`, `Complexity.clHeaderField_native`, `Complexity.clHeaderTail_native`, `Complexity.clA5Field_native`, `Complexity.clA5Sizes_native`, `Complexity.clA5SmallNum_native`.
