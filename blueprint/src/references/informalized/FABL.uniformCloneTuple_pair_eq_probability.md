<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.uniformCloneTuple_pair_eq_probability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collision probability for a uniform tuple

**Claim.** For $r,M\in\mathbb N$ with $M>0$ and distinct coordinates $i,j\in\{0,\ldots,r-1\}$, a uniformly chosen tuple in $\{0,\ldots,M-1\}^r$ has probability $1/M$ of agreeing at those two coordinates.

**Proof.** Reindex the tuple by a bijection that records its entries at the two distinguished coordinates first and places all remaining entries in a tuple of residual coordinates. A bijection preserves uniform expectation, so the desired probability becomes the probability that the first two entries of a uniformly chosen product tuple in $\{0,\ldots,M-1\}\times\{0,\ldots,M-1\}\times R$ agree. Average first over the residual tuple, which does not affect the event, and then over the second distinguished entry while fixing the first. Exactly one of the $M$ possible second entries matches the fixed first entry, giving probability $1/M$.

**Key facts.** `FABL.fintype_expect_prod`.
