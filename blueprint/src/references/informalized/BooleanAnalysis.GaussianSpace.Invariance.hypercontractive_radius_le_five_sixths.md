<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdMoments.lean :: BooleanAnalysis.GaussianSpace.Invariance.hypercontractive_radius_le_five_sixths -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound on the hypercontractive radius

**Claim.** Under the stated probability, mean, variance, and $(2,3,\rho)$-hypercontractivity assumptions, the hypercontractive radius satisfies $\rho\le 5/6$.

**Proof.** The squared-radius estimate gives $\rho^2\le 2/3$. Since $\rho>0$, it follows that $\rho$ is at most $\sqrt{2/3}$. Finally, $\sqrt{2/3}\le 5/6$, as is seen by squaring both positive quantities and comparing $2/3\le25/36$.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.hypercontractive_radius_sq_le`.
