<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/UniformTransfer.lean :: BooleanAnalysis.GaussianSpace.tendsto_booleanBlockExpectation_real -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Boolean block expectation convergence

**Claim.** The weighted real-valued Boolean block averages converge to the integral of the test function under the correlated Gaussian law.

**Proof.** Regard the real-valued test function $F$ as a complex-valued continuous function by composing it with the inclusion $r\mapsto r+i0$. Apply the complex Boolean block expectation convergence theorem to this function. The formula for the finite Boolean expectation (`booleanBlockExpectation_apply`) identifies each term with the stated weighted sum after embedding the real factors into $\mathbb C$. The complex integral of a real-valued function is its real integral embedded in $\mathbb C$. Taking real parts of the resulting convergence therefore gives the asserted real convergence.

**Key facts.** `BooleanAnalysis.GaussianSpace.booleanBlockExpectation_apply`, `BooleanAnalysis.GaussianSpace.tendsto_booleanBlockExpectation`.
