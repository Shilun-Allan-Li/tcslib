<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_vwid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Width Bound

**Claim.** The function sending $y$ to a unary string of length $A(|x|+1)^a$, where $x$ is the decoded first component of $y$, is polynomial-time computable.

**Proof.** The polynomial unary-length construction computes, from any string $x$, a unary string of length $A(|x|+1)^a$ (`polyTimeComputable_polyUnary`). The first-component decoder is polynomial-time computable (`polyTimeComputable_pairFstD`). Composing these operations gives the desired function of $y$ (`PolyTimeComputable.comp`).

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`.
