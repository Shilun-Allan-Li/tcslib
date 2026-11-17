<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordRestrictionProductWeight_reindex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance under reindexing

**Claim.** Transporting a coordinate restriction assignment along a bijection between finite index sets leaves its product weight unchanged.

**Proof.** Expand both product weights as products of the coordinate weights. Reindex the product over $K$ along the bijection $e$, so its terms are indexed by $I$ and the term at $i$ is the weight of $\rho(i)$, because $e^{-1}(e(i))=i$. This is precisely the product over $I$, proving the equality.
