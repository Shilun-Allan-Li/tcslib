<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.expect_maxLinearPredicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability of a nonzero linear predicate

**Claim.** A uniformly random assignment to the variables of a linear equation over $\mathbb F_2$ with at least one variable satisfies the equation with probability $1/2$, for any right-hand side.

**Proof.** The positive arity assumption rules out zero variables, so write the assignment as a head bit and a tail assignment. A coordinate-splitting bijection and product averaging express the acceptance probability by first averaging over the head bit and then over the tail. For each fixed tail, its sum contributes a fixed offset to the equation. Exactly one of the two head-bit values makes the equation equal the prescribed right-hand side, so the inner acceptance probability is $1/2$ (`FABL.expect_f₂_add_eq`). Averaging this constant over all tails leaves it equal to $1/2$.

**Key facts.** `FABL.expect_f₂_add_eq`.
