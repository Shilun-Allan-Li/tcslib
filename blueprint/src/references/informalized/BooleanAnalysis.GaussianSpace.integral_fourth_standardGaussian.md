<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InputMoments.lean :: BooleanAnalysis.GaussianSpace.integral_fourth_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian fourth moment

**Claim.** The fourth moment of the standard Gaussian measure on $\mathbb R$ is $3$.

**Proof.** Use the identity relating moments to derivatives of the moment-generating function at zero (\texttt{iteratedDeriv_mgf_zero}) to express the fourth moment as the fourth derivative at zero of the Gaussian moment-generating function. That generating function is $t\mapsto e^{t^2/2}$ (\texttt{mgf_fun_id_gaussianReal}). To compute its fourth derivative, differentiate successively: the first three derivatives are $te^{t^2/2}$, $(1+t^2)e^{t^2/2}$, and $(3t+t^3)e^{t^2/2}$. Differentiating once more and evaluating at zero gives $3$.

**Caveat.** The proof uses two upstream probability results that are invoked in its source but are not listed in the supplied upstream field.
