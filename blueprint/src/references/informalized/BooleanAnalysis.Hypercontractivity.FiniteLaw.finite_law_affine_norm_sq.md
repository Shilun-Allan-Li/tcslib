<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/FiniteLaw.lean :: BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_law_affine_norm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-law affine norm

**Claim.** For a measurable real-valued random variable supported almost everywhere on a finite set, the squared norm of its affine transform is the finite sum of its atom weights times the corresponding absolute moments, raised to the power $2/q$.

**Proof.** First, the almost-everywhere finite-range condition gives the random variable a lower bound on its atoms, so the affine transform belongs to the required $L^q$ space by the finite-atom integrability result ( `HasAtomLowerBound.memLp` ). The norm-to-moment identity (`rvLpNorm_rpow`) then expresses the $q$th power of its norm as the integral of $|a+bX|^q$. Applying the finite-law integral formula (`finite_law_integral`) evaluates that integral as the sum over $x\in s$ of the mass of the event $X=x$ times $|a+bx|^q$. Finally, since the norm is nonnegative, the real-power laws convert this identity for the $q$th power into the claimed identity for its square; the remaining exponent simplification uses $q>0$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.HasAtomLowerBound.memLp`, `BooleanAnalysis.Hypercontractivity.rvLpNorm_rpow`, `BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_law_integral`.
