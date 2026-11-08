<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.normalizedRademacherSum_secondMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment of the Normalized Sum

**Claim.** For every positive natural number $n$, the second moment of the normalized sign sum on the cube is $1$.

**Proof.** The second moment formula for a linear form on the uniform sign cube identifies its expectation of the square with the sum of the squared coefficients (`FABL.expect_linearForm_sq`). Here all $n$ coefficients are $(\sqrt n)^{-1}$, so this sum is $n(\sqrt n)^{-2}$. Positivity of $n$ gives $(\sqrt n)^2=n$, and hence the expression equals $1$.

**Key facts.** `FABL.expect_linearForm_sq`.
