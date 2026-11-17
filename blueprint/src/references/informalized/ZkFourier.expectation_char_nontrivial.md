<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.expectation_char_nontrivial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Nontrivial Character

**Claim.** For a nonzero index vector $s$, the uniform expectation of its Fourier character is zero.

**Proof.** First factor the sum of the character over all vectors into a product of coordinate sums. The vectors range over a finite product, and the character of a vector is the product of its one-coordinate contributions; multiplicativity of the root-of-unity map, expressed by `toOmega_add`, gives this factorization. Since $s\ne 0$, some coordinate $i$ has $s_i\ne 0$. The corresponding factor is the sum of $\mathrm{toOmega}(s_i x_i)$ over all residues $x_i$. The geometric-sum identity `geom_sum_toOmega` makes this factor zero when $s_i\ne 0$, so the whole product, and hence the original character sum, vanishes. Dividing by the size of the vector space in the definition of expectation preserves the value zero.

**Key facts.** `ZkFourier.toOmega_add`, `ZkFourier.geom_sum_toOmega`.
