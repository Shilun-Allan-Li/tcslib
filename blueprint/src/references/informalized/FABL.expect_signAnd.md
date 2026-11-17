<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.expect_signAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the conjunction of two signs

**Claim.** For independent uniform signs, the sign that is $-1$ exactly when both inputs are $-1$ has expected value $1/2$.

**Proof.** Average over the four equally likely input pairs. The conjunction is $-1$ on the single pair $(-1,-1)$ and $1$ on the other three pairs. Its mean is therefore $(-1+1+1+1)/4=1/2$.
