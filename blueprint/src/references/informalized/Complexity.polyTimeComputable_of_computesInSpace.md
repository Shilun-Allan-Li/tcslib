<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Complexity.polyTimeComputable_of_computesInSpace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Log-space computation implies polynomial time

**Claim.** A function computed by a finite Turing machine that halts on every input and uses at most a constant multiple of $\log_2 |x|+1$ work-tape cells is polynomial-time computable.

**Proof.** The log-space-to-time theorem for finite Turing machines states that any machine satisfying this space bound computes its function within a polynomial time bound. In particular, the time bound has the form $A(n+1)^d$, with constants determined by the machine and the space-bound constant. Apply this theorem to the assumed machine. Its resulting polynomial-time computation is exactly the given function, which establishes polynomial-time computability.

**Key facts.** `Turing.FinTM.ComputesInSpace.computesFunInTime`.
