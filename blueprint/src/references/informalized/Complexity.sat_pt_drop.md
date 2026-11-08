<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Projected Suffix Extraction

**Claim.** For a binary word $z$, decode it as a pair using the aligned pair parser, taking either projection to be empty if decoding fails. The function returning the second projection after removing its first as many bits as the length of the first projection is polynomial-time computable.

**Proof.** First compute both total projections in polynomial time, and pair-encode them; the resulting word has length bounded by the running-time polynomial for this encoding machine, since a machine's output length is at most its running time (`Turing.MultiTapeTM.output_length_le`). Next, on that encoded pair, use the machine that extracts the second component after dropping as many bits as the first component has length; this takes at most three times the encoded length plus one (`Complexity.satDrop_computes`). The composition theorem for computation on an image combines these machines, charging for the first computation and the extraction on its output (`Complexity.sat_comp_on_image`). Finally, the resulting time bound is polynomial in $|z|$: since $(|z|+1)^e\geq 1$, the fixed additive constants can be absorbed into the coefficient, giving the displayed polynomial bound with coefficient $5C+5$ and exponent $e$.

**Key facts.** `Complexity.sat_pt_fields`, `Complexity.sat_pt_pair`, `Turing.MultiTapeTM.output_length_le`, `Complexity.satDrop_computes`, `Complexity.sat_comp_on_image`, `Turing.FinTM.ComputesInTime.mono`.
