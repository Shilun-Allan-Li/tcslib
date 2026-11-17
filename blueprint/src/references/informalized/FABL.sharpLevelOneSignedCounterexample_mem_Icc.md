<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.sharpLevelOneSignedCounterexample_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of a two-coordinate linear form

**Claim.** For each $x\in\{-1,1\}^2$, the value of the linear form with both coefficients equal to $1/2$ lies in $[-1,1]$.

**Proof.** Each coordinate sign is either $-1$ or $1$ (the two-valued sign property, `signValue_eq_neg_one_or_one`). Therefore the linear form is one of $-1,0,1$: it is half the sum of the two coordinate signs. Each possibility lies in the stated interval.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`.
