<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_prepend -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Fixed Prepending

**Claim.** For every fixed bit string $w$, the function sending a bit string $x$ to the concatenation $wx$ is polynomial-time computable.

**Proof.** A machine that prepends the fixed word $w$ computes the function in linear time: the supplied computation theorem gives a bound $c(|x|+1)$ for some $c$ (`computesFunInTime_prepend`). The general implication from linear-time computability to polynomial-time computability (`polyTimeComputable_of_linear`) then proves the claim.

**Key facts.** `Turing.FinTM.computesFunInTime_prepend`, `Complexity.polyTimeComputable_of_linear`.
