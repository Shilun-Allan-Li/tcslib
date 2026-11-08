<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean :: BooleanAnalysis.Hypercontractivity.hypercontractivity_2_6 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sixth-Moment Hypercontractivity

**Claim.** If $\rho^2\le1/5$, then the sixth moment of the noise operator applied to $f$ is at most the cube of the second moment of $f$.

**Proof.** Use the even-moment theorem `hypercontractivity_2_q` with $q=6$. The numerical conditions hold because $6\ge2$ and $6$ is even. Its noise constraint is $\rho^2\le1/(6-1)=1/5$, precisely the hypothesis here, and its right-hand exponent is $6/2=3$. Substituting these values gives the asserted inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.hypercontractivity_2_q`.
