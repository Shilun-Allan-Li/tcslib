<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.two_pow_eq_one_add_sum_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite geometric sum for powers of two

**Claim.** For every natural number $d$, interpreting natural-number powers as real numbers, $2^d=1+\sum_{j=0}^{d-1}2^j$.

**Proof.** The finite geometric-series identity in the natural numbers, specialized to ratio $2$ and length $d$, gives $2^d=1+\sum_{j=0}^{d-1}2^j$. Casting this identity into the real numbers preserves the equality.
