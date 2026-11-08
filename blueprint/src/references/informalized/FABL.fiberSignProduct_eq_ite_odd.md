<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.fiberSignProduct_eq_ite_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Product Over a Fiber

**Claim.** The product of the sign at $j$ over indices $i\in S$ with $\pi(i)=j$ equals that sign when the number of such indices is odd, and equals $1$ when it is even.

**Proof.** The product repeats the same value $s=w(j)$ once for each index in the fiber, so it equals $s^q$, where $q$ is the size of the fiber. A sign has value either $-1$ or $1$ (`signValue_eq_neg_one_or_one`). If $s=1$, the product is always $1$, agreeing with either parity case. If $s=-1$, its $q$th power is $-1$ for odd $q$ and $1$ for even $q$, giving the claimed formula.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`.
