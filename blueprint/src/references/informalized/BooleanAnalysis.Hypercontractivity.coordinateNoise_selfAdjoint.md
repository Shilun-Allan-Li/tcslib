<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Contraction.lean :: BooleanAnalysis.Hypercontractivity.coordinateNoise_selfAdjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-adjointness of coordinate noise

**Claim.** For every finite product $P$, coordinate $i$, real parameter $\rho$, and functions $f,g$, the expectation of $(N_{i,\rho}f)g$ equals the expectation of $f(N_{i,\rho}g)$.

**Proof.** Write $C f$ for the conditional expectation over coordinate $i$, with the other coordinates fixed. The conditional expectation self-adjointness identity gives $\mathbb E[(C f)g]=\mathbb E[f(C g)]$. Also, from $L_i f=f-Cf$, the noise operator can be written $N_{i,\rho}f=\rho f+(1-\rho)Cf$. Thus the left-hand side is $\rho\mathbb E[fg]+(1-\rho)\mathbb E[(Cf)g]$, while the right-hand side is $\rho\mathbb E[fg]+(1-\rho)\mathbb E[f(Cg)]$. These are equal by the conditional expectation identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_selfAdjoint`.
