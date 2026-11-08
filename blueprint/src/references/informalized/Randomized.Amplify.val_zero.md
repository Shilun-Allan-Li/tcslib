<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.val_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Block Acceptance Value

**Claim.** With zero blocks, the acceptance value at offset $c$ is $1$ when the decision function sends $c$ to $v$, and is $0$ otherwise.

**Proof.** Unfold the acceptance value. Since the number of random bits is $0\cdot T=0$, the value is the probability of the constant predicate that $\operatorname{dec}(c)=v$. The constant-predicate formula for the random probability (`Randomized.randProb_const`) identifies this probability with $1$ if the predicate holds and $0$ otherwise. The defining predicate for zero blocks is indeed constant in the random string: its block count is zero, so the decision input is just $c$.

**Key facts.** `Randomized.randProb_const`.
