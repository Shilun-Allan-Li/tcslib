<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.normalizedRademacherSum_fourthMoment_le_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Moment Bound

**Claim.** For every positive natural number $n$, the fourth moment of the normalized Rademacher sum on the sign cube is at most $3$.

**Proof.** Apply the fourth moment formula for a linear form on the uniform sign cube (`FABL.expect_linearForm_fourth`). With all $n$ coefficients equal to $(\sqrt n)^{-1}$, each sum of squared coefficients is $n(\sqrt n)^{-2}$, and the sum of fourth powers is $n(\sqrt n)^{-4}$. Since $n>0$, we have $(\sqrt n)^2=n$ and can simplify these expressions to obtain the moment $3-2/n$. As $n$ is positive, $2/n>0$, so this is at most $3$.

**Key facts.** `FABL.expect_linearForm_fourth`.
