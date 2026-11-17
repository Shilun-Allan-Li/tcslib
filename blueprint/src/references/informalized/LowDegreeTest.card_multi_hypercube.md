<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.card_multi_hypercube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of hypercube tuples

**Claim.** The set of $k$-tuples of points of the Boolean hypercube of dimension $n$ has cardinality $2^{nk}$.

**Proof.** A tuple of $k$ hypercube points is a function from a $k$-element index set into the hypercube. The cardinality of a function space is the cardinality of the codomain raised to the cardinality of the domain, so this set has size $(2^n)^k$, using the hypercube cardinality formula (`card_hypercube`). The exponent laws give $(2^n)^k=2^{nk}$.

**Key facts.** `BoolFourier.card_hypercube`.
