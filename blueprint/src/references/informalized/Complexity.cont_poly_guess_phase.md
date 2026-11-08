<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_poly_guess_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Length Choice Scheduling

**Claim.** For every $C,c\in\mathbb N$, there is a deterministic machine and a polynomial time bound such that, on the all-$1$ input of length $n$, every choice word of the prescribed time length captures a word of length $C(n+1)^c$, and every word of that length can be captured by some choice word of that time length.

**Proof.** Use the polynomial-time construction theorem (`Turing.FinTM.computesFunInTime_polyUnary`) with parameters $C,c$. It supplies a machine $M$ and a time coefficient $A$ whose computed output on an input of length $n$ is the all-$1$ word of length $C(n+1)^c$, in time $A(n+1)^{c+1}$. Apply the choice-coverage result (`Complexity.cont_guess_coverage`) to this computation, taking the input to be the all-$1$ word of length $n$ and the computed word to be the all-$1$ word of the required length. That result gives both directions: every choice word of the exact time length has a corresponding captured word of the output length, and every word of that output length is captured by some choice word of the exact time length. The length of the all-$1$ output is the specified polynomial by the definition of replication.

**Key facts.** `Turing.FinTM.computesFunInTime_polyUnary`, `Complexity.cont_guess_coverage`.
