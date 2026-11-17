<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DiscreteDerivatives.lean :: FABL.discreteDerivative_ne_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero Discrete Derivative Criterion

**Claim.** The discrete derivative of $f$ in coordinate $i$ at $x$ is nonzero exactly when the values of $f$ at the two points obtained by setting that coordinate to $1$ and $-1$ are unequal.

**Proof.** By definition, the derivative is the difference of those two values divided by $2$. Since $2$ is nonzero in the reals, this quotient is nonzero exactly when the difference is nonzero; a difference is nonzero exactly when its two terms are unequal.
