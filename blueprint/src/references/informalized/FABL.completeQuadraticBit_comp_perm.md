<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadraticBit_comp_perm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation invariance of the quadratic bit

**Claim.** Permuting the coordinates of a vector in $\mathbb{F}_2^n$ does not change its complete quadratic bit.

**Proof.** By the unordered-pair formula for the complete quadratic bit ( `completeQuadraticBit_eq_sym2_sum`), it is enough to compare the sums over nondiagonal unordered pairs of coordinates. The permutation $\pi$ induces a bijection on unordered pairs, with inverse induced by $\pi^{-1}$. This bijection preserves the property of being nondiagonal, since a pair is diagonal exactly when its two coordinates agree, and $\pi$ is injective. Under this reindexing, the product attached to a pair for the permuted vector is the product attached to its image for the original vector: the lift from ordered pairs to unordered pairs is well-defined because multiplication in $\mathbb{F}_2$ is commutative. Thus the two finite sums agree.

**Key facts.** `FABL.completeQuadraticBit_eq_sym2_sum`.
