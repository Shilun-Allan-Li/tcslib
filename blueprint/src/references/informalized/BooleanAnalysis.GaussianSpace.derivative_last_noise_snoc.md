<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Noise.lean :: BooleanAnalysis.GaussianSpace.derivative_last_noise_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last derivative of the noise operator

**Claim.** At a point formed by appending a bit to $x$, the last-coordinate derivative of the noise operator applied to $f$ equals $\rho$ times the noise operator applied to the last-coordinate half-difference of $f$, evaluated at $x$.

**Proof.** The last-derivative identity says that the derivative at the appended point is the last-coordinate half-difference of the function there. Apply the noise-operator decomposition for an appended bit to each of the two restrictions defining that half-difference. The terms involving the average over the last coordinate cancel; the difference terms combine with the factor $1/2$ to give $\rho$ times the noise operator of the last-coordinate half-difference at $x$. The bit-sign identities, which give $1$ for false and $-1$ for true, make this cancellation and combination hold for either appended bit.

**Key facts.** `BooleanAnalysis.GaussianSpace.derivative_last_snoc`, `BooleanAnalysis.Hypercontractivity.noiseOp_snoc`, `BooleanAnalysis.boolToSign_false`, `BooleanAnalysis.boolToSign_true`.
