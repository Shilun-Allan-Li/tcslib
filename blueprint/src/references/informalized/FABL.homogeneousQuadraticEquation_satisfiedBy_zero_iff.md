<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.homogeneousQuadraticEquation_satisfiedBy_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Dimensional Quadratic Equation

**Claim.** For a homogeneous quadratic equation on the zero-dimensional binary cube, its unique vector satisfies the equation exactly when the right-hand side is zero.

**Proof.** When the dimension is zero, there are no indices in either matrix sum defining the pairing. The pairing of the coefficient matrix with the rank-one matrix is therefore the empty sum, hence zero. Thus satisfaction is precisely the equality $0=\mathrm{rhs}$, equivalent to $\mathrm{rhs}=0$.
