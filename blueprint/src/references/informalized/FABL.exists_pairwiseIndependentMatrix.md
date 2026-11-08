<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/PairwiseIndependence.lean :: FABL.exists_pairwiseIndependentMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a Pairwise Independent Matrix

**Claim.** Under the stated bound on $n$ and $\ell$, there exists a binary matrix whose every nonempty sum of at most two columns is nonzero.

**Proof.** Take the matrix constructed as `pairwiseIndependentMatrix hn`. The established column-sum property for this construction says that every nonempty sum of at most two of its columns is nonzero (`pairwiseIndependentMatrix_hasNonzeroColumnSumsUpTo`). This matrix therefore witnesses the required existence.

**Key facts.** `FABL.pairwiseIndependentMatrix_hasNonzeroColumnSumsUpTo`.

**Caveat.** The supplied formal statement concerns sums of at most two columns and assumes $n\le 2^\ell-1$; it does not state the more general Theorem 6.32 construction described in the informal text.
