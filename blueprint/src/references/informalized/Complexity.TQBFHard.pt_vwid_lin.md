<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_vwid_lin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Quadratic Width Expression

**Claim.** For $V=A(|x|+1)^a$, the function sending $y$ to a unary string of length $kV^2+lV$ is polynomial-time computable.

**Proof.** The first summand has length $kA^2(|x|+1)^{2a}$, so the polynomial unary-length construction, composed with the first-component decoder, computes its unary encoding in polynomial time (`polyTimeComputable_polyUnary`, `polyTimeComputable_pairFstD`, `PolyTimeComputable.comp`). The same construction computes the unary encoding of the second summand $lA(|x|+1)^a$ (`polyTimeComputable_polyUnary`, `polyTimeComputable_pairFstD`, `PolyTimeComputable.comp`). Concatenate these two unary outputs using closure under append (`PolyTimeComputable.append`). Their lengths add to $kV^2+lV$, since $V=A(|x|+1)^a$ and exponentiation gives $(|x|+1)^{2a}=(|x|+1)^a(|x|+1)^a$.

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.append`.
