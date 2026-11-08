<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_polyUnary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Output

**Claim.** For every $C,d\in\mathbb{N}$, the function sending a bit string $x$ to the word consisting of $C(|x|+1)^d$ copies of $1$ is polynomial-time computable.

**Proof.** The unary-output computation theorem supplies a machine computing the required word in time $c(|x|+1)^{d+1}$ for some natural number $c$ (`computesFunInTime_polyUnary`). This is already a polynomial time bound, so choose polynomial exponent $d+1$ and coefficient $c$ in the definition of polynomial-time computability.

**Key facts.** `Turing.FinTM.computesFunInTime_polyUnary`.
