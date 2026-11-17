<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadraticBit_eq_sym2_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic bit as a sum over unordered pairs

**Claim.** The complete quadratic bit of $x\in\mathbb{F}_2^n$ is the sum of $x_i x_j$ over all unordered pairs of distinct coordinates.

**Proof.** The sum over unordered pairs of distinct coordinates can be represented by choosing the unique ordered representative $(i,j)$ with $i<j$. First, rewrite the inner sum over $j\in Ioi(i)$ as a sum over all coordinates, with summand $x_i x_j$ when $i<j$ and zero otherwise. Summing over $i$ then gives a sum over all ordered pairs. Filtering this sum to the pairs with $i<j$ leaves exactly those terms, and each such pair contributes the unordered-pair product $x_i x_j$. Finally, these representatives are precisely the off-diagonal ordered pairs satisfying $i<j$, so the sum is the stated sum over nondiagonal unordered pairs.
