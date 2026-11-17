<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_sq_eq_expect_odd_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment of a Sign Decomposition

**Claim.** If $f(b,x)=b\,d(x)+e(x)$ for each sign $b$ and cube point $x$, then the uniform second moment of $f$ is the sum of the uniform second moments of $d$ and $e$.

**Proof.** First average over the leading sign using the decomposition of expectation by the first coordinate (FABL.expect_fin_cons). The two slices are $d(x)+e(x)$ and $-d(x)+e(x)$. Their squares expand as $d(x)^2+2d(x)e(x)+e(x)^2$ and $d(x)^2-2d(x)e(x)+e(x)^2$. Averaging these expressions over $x$, the mixed terms cancel, while the two copies of each square term, divided by $2$, leave exactly the means of $d^2$ and $e^2$.

**Key facts.** `FABL.expect_fin_cons`.
