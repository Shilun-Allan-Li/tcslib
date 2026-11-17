<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceExtensions.lean :: BooleanAnalysis.GaussianSpace.invariance_c3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third-Order Invariance Estimate

**Claim.** Under the stated independence, hypercontractivity, moment, degree, and derivative-bound hypotheses, the difference between the expectations of $\psi(F(X))$ and $\psi(F(Y))$ is bounded by the stated influence sum.

**Proof.** First place both coordinate families on a single probability space. The independent polynomial coupling theorem (`independent_polynomial_coupling`) supplies a jointly independent family whose left coordinates have the laws of the $X_i$, whose right coordinates have the laws of the $Y_i$, and whose two polynomial evaluations have the corresponding laws. Transfer each coordinate's hypercontractivity to this common space by invariance under equality in distribution (`IsHypercontractive.identDistrib`). The same equality in distribution transfers the zero means and unit second moments. Applying it to the polynomial evaluations after composition with the continuous function $\psi$ identifies the original two integrals with the integrals of the two coupled evaluations. Now apply the independent-pair third-order invariance theorem (`invariance_c3_of_independent_pair`) to the coupled family. It gives exactly the claimed bound, with the original degree, derivative bound, and influences.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.independent_polynomial_coupling`, `BooleanAnalysis.Hypercontractivity.IsHypercontractive.identDistrib`, `BooleanAnalysis.GaussianSpace.Invariance.invariance_c3_of_independent_pair`.
