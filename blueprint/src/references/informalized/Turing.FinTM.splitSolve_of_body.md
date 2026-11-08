<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitSolve_of_body -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split Solver from a Round Contract

**Claim.** Under the stated initialization and round hypotheses for a body machine, some finite Boolean Turing machine computes the encoded least valid split, or the empty word when no candidate is valid, within $c(|w|+1)^{e+2}$ steps for some natural number $c$.

**Proof.** Choose a finite machine computing the binary expansion of the input length, as guaranteed by `computesFunInTime_lengthBits`. Increase its linear time bound to $(A+a)(n+1)^{e+1}$: the inequality $n+1\le(n+1)^{e+1}$ absorbs its original linear cost into the body’s polynomial scale. The assumed initialization and round bounds can likewise be enlarged from $A$ to $A+a$. Now apply the loop-finding construction (`exists_loopFindTM`) to the body, using the candidate-length invariant, the operation that appends one bit when the candidate is still short, and the given acceptance test. Its hypotheses are exactly the initialized anchor configuration, the bounded non-returning rounds, and the length-counter fuel bound just established. This yields a machine that searches candidates and returns the required encoded pair at the first acceptance, or the empty word if none accepts. The identification of this loop’s output with the least-split specification is `splitLoop_result`. Finally, `splitLoop_bound` converts the loop’s bound into $2c(A+a+1)(|w|+1)^{e+2}$; choosing this coefficient as the existential constant proves the claim.

**Key facts.** `Turing.FinTM.computesFunInTime_lengthBits`, `Turing.FinTM.exists_loopFindTM`, `Turing.FinTM.splitLoop_result`, `Turing.FinTM.splitLoop_bound`.
