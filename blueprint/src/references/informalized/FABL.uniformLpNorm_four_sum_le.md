<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.uniformLpNorm_four_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triangle inequality for finite sums

**Claim.** For a finite nonempty set $\Omega$, a finite subset $s\subseteq\iota$, and functions $f_i:\Omega\to\mathbb R$, the uniform $L^4$ norm of $x\mapsto\sum_{i\in s}f_i(x)$ is at most $\sum_{i\in s}\|f_i\|_4$.

**Proof.** Induct on the finite set $s$. For the empty set, the summed function and the sum of norms are both zero. For the inductive step, write $s$ as the disjoint union of a new element $a$ and the previous set. The function summed over $s$ is the pointwise sum of $f_a$ and the function summed over the previous set. The triangle inequality for the uniform $L^4$ norm (uniformLpNorm_four_add_le) bounds its norm by the sum of their norms. Applying the induction hypothesis to the second term gives the desired bound.

**Key facts.** `FABL.uniformLpNorm_four_add_le`.
