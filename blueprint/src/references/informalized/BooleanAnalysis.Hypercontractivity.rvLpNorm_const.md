<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.rvLpNorm_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Norm of a constant random variable

**Claim.** On a probability space, if $q>0$, then the norm of the constant function with value $c$ is $N_q(c)=|c|$.

**Proof.** By the formula for the extended $L^q$ norm of a constant function, its norm is $|c|$ times the $q$th root of the total measure. The measure is a probability measure, so its total mass is $1$; hence this root is $1$, and the norm equals $|c|$.
