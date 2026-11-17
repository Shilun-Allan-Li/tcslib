<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean :: Complexity.BinArith.guardLoop_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guard Loop Outcomes

**Claim.** The result of the guard loop on $W$ is either the fixed completed-block encoding or the encoding whose first component is $\pi_1(W)$ and whose second component pairs the tail of $\pi_1(\pi_2(W))$ with the guarded next-state value at $\pi_1(W)$ and $\pi_2(\pi_2(W))$.

**Proof.** Unfold the guard loop and its block step. The step tests whether its first decoded component is empty and, if not, whether the first component of its decoded second component is empty. In either case it returns the fixed completed-block encoding. If both tests fail, the step returns the stated pair encoding, using the identity update on the first component and the guarded next-state function on the decoded data. These branches exhaust the possibilities, so the result is one of the two claimed forms.
