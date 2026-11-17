<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LevelOneInequality.lean :: FABL.uniformRademacher_abs_linearForm_gt_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rademacher Linear Form Tail Bound

**Claim.** If the coefficients satisfy $\sum_i a_i^2=1$, then for every $t\ge 0$, a uniformly random sign vector satisfies $\Pr(t<|L(x)|)\le 2e^{-t^2/2}$.

**Proof.** The normalization implies $a_i^2\le \sum_j a_j^2=1$ for each $i$, since every square is nonnegative; hence $|a_i|\le 1$. Apply the Rademacher tail estimate with coefficient bound $1$ (`exercise5_31a`), which bounds the probability of the closed-tail event $t\le |L(x)|$ by $2e^{-t^2/2}$. The event $t<|L(x)|$ is contained in that closed-tail event, so monotonicity of probability gives the claimed bound.

**Key facts.** `FABL.exercise5_31a`.

**Caveat.** The informal statement describes a tail-weighted expectation and assumes $s\ge1$, whereas the formal statement and proof establish the tail probability bound above for $t\ge0$.
