<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_bits_vrad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Radius Bits

**Claim.** The function sending $y$ to the binary-list representation of $2d(|x|+1)^c$, where $x$ is extracted from $y$, is polynomial-time computable.

**Proof.** The extracted component $x$ is polynomial-time computable (`polyTimeComputable_pairFstD`). The numerical function $n\mapsto 2d(n+1)^c$ is a polynomial in the input length, so the polynomial-unary construction produces a word of that many true bits in polynomial time (`polyTimeComputable_polyUnary`). Compose these functions to obtain a polynomial-time output encoding the value $2d(|x|+1)^c$. The standard length-to-binary-bits machine computes the binary-list representation of the length of a unary word in linear time (`computesFunInTime_lengthBits`), and hence is polynomial-time computable (`polyTimeComputable_of_linear`). Composing it with the preceding computation gives the desired bits; unfolding the radius definition identifies the value with $vrad(d,c,|x|)$ (`PolyTimeComputable.comp`).

**Key facts.** `Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.polyTimeComputable_of_linear`, `Complexity.polyTimeComputable_polyUnary`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairFstD`.
