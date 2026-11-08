<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHard.lean :: Complexity.TQBFHard.pt_redM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Output Length

**Claim.** For every finite nondeterministic Turing machine $N$, natural numbers $d,c$, and the stated parameters, the function outputting a string of $3R(|x|)^2+3R(|x|)$ ones is polynomial-time computable, with $R(n)=W(n)(n+1)^{c+1}$.

**Proof.** The length $3R(n)^2$ is the polynomial $3W(n)^2(n+1)^{2(c+1)}$, so the corresponding unary string is polynomial-time computable by `polyTimeComputable_polyUnary`. The length $3R(n)$ is likewise $3W(n)(n+1)^{c+1}$ and has a polynomial-time unary output by the same result. Concatenate the two unary strings using polynomial-time closure under appending (`PolyTimeComputable.append`). Their concatenation consists entirely of ones and has length $3R(n)^2+3R(n)$, as required.

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.PolyTimeComputable.append`.
