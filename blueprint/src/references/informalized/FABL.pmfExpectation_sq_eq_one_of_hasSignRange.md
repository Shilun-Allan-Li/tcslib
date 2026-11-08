<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.pmfExpectation_sq_eq_one_of_hasSignRange -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment of a Sign-Valued Function

**Claim.** If $f$ takes only the values $-1$ and $1$, then its squared value has expectation $1$.

**Proof.** At each point, the sign-range assumption gives either $f(x)=-1$ or $f(x)=1$, and in either case $f(x)^2=1$. Thus the squared function is the constant function $1$. The expectation of a constant (`pmfExpectation_const`) is that constant, so the expectation is $1$.

**Key facts.** `FABL.pmfExpectation_const`.
