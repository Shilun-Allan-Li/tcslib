<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.executableSmallBiasConstructionWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-Bias Construction Work

**Claim.** For natural numbers $n$ and $\ell$, executable small-bias construction work is the field preprocessing work for dimension $\ell$ plus $2^{2\ell}$ times one more than the row work for $n$ rows and dimension $\ell$.

**Proof.** By the traversal-work identity (FABL.binaryConstructorTraversalWork_eq), the final traversal contributes the length of the list of ordered pairs of binary vectors, multiplied by one more than the row work. The pair-list length identity (FABL.length_binaryVectorPairs) evaluates that length as $2^{2\ell}$. Adding the unchanged field preprocessing term yields the stated formula.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`, `FABL.length_binaryVectorPairs`.
