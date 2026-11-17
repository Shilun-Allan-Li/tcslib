<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.card_matrixRowSpan_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix row span cardinality bound

**Claim.** For an $m$-by-$n$ matrix $H$ over the field with two elements, the row span of $H$ has at most $2^m$ elements.

**Proof.** A finite-dimensional subspace over the two-element field with dimension $r$ has exactly $2^r$ elements (`card_submodule_eq_two_pow_finrank`). The row span is the range of the linear map sending a vector of $m$ coefficients to the corresponding linear combination of the rows. Its dimension is at most the dimension of the domain, which is $m$. Hence its cardinality is $2^r\le 2^m$.

**Key facts.** `FABL.card_submodule_eq_two_pow_finrank`.
