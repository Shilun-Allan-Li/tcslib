<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.prod_f₂Cube_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting a Product over a Binary Cube

**Claim.** The product of a function over the binary cube of dimension $k+1$ equals the product over the two slices with final coordinate $0$ and $1$.

**Proof.** Use the bijection that writes each $(k+1)$-tuple uniquely as a $(k$-tuple, final coordinate). Reindexing the product by this bijection expresses it as an iterated product: first over the final coordinate and then over the $k$-tuples. The final coordinate has exactly the two values $0$ and $1$, so this iterated product is the product over the zero slice times the product over the one slice, as claimed.
