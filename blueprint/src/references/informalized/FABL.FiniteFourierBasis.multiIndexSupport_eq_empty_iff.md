<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.multiIndexSupport_eq_empty_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty support and zero multi-index

**Claim.** The support of a multi-index is empty exactly when every coordinate has the distinguished zero index, or equivalently when the multi-index is the zero multi-index.

**Proof.** Suppose first that the support is empty. If some coordinate had an index different from the distinguished zero index, that coordinate would belong to the support by its definition, a contradiction. Hence every coordinate has the distinguished index, so the multi-index equals the zero multi-index. Conversely, if the multi-index is the zero multi-index, no coordinate differs from the distinguished index, and its support is empty.
