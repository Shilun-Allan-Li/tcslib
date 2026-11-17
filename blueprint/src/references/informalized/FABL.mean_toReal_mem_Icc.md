<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_toReal_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Sign-Valued Function

**Claim.** The mean of the real-valued function obtained from a sign-valued function on the sign cube lies in $[-1,1]$.

**Proof.** Write the mean as the sum of the function’s values divided by the cardinality of the cube, which is positive. Every output sign is either $-1$ or $1$, so its real value is at least $-1$ and at most $1$. Summing these pointwise bounds over the cube bounds the total sum between $-1$ times the cardinality and $1$ times the cardinality. Dividing by the positive cardinality gives the claimed interval bound.
