<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.goldreichLevinActiveInvariant_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Active Family

**Claim.** If every frequency set whose Fourier coefficient has magnitude at least $\tau$ has its length-$n$ prefix in the active family, then every such frequency set belongs to the active family.

**Proof.** Take a frequency set $U$ with $|\widehat f(U)|\ge\tau$. The invariant's completeness condition says that the length-$n$ prefix of $U$ belongs to the active family. Since $U$ is a subset of the $n$ coordinates, its length-$n$ prefix is exactly $U$; hence $U$ belongs to the family (`prefixFrequency_eq_self`).

**Key facts.** `FABL.prefixFrequency_eq_self`.
