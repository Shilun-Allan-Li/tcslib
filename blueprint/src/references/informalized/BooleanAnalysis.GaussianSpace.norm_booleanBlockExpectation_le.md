<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/UniformTransfer.lean :: BooleanAnalysis.GaussianSpace.norm_booleanBlockExpectation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean block expectation norm bound

**Claim.** For $0\leq\rho\leq1$, the norm of the Boolean block expectation of a continuous complex-valued function on the stated torus is at most the supremum norm of that function.

**Proof.** First express the block expectation as its finite weighted sum over pairs of Boolean inputs (`booleanBlockExpectation_apply`). Regard the value of the continuous function at the Gaussian-torus image of each pair as a function of those inputs. Its complex norm is bounded by the supremum norm of the original continuous function, by the definition of the supremum norm. The norm bound for Boolean noise averaging (`norm_booleanNoiseExpectation_le`) then bounds the norm of the weighted sum by that same supremum norm.

**Key facts.** `BooleanAnalysis.GaussianSpace.booleanBlockExpectation_apply`, `BooleanAnalysis.GaussianSpace.norm_booleanNoiseExpectation_le`.
