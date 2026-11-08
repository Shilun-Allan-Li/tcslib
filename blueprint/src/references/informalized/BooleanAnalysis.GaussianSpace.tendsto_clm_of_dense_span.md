<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/UniformTransfer.lean :: BooleanAnalysis.GaussianSpace.tendsto_clm_of_dense_span -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence from a dense span

**Claim.** If the functionals are uniformly bounded by a common multiple of the norm and converge on a set whose complex linear span is dense, then they converge pointwise everywhere.

**Proof.** First, the common bound on $L_m(x-y)=L_m(x)-L_m(y)$ gives a uniform continuity modulus: for every $m$, the change in $L_m$ between two points is at most $C$ times their distance. Next prove convergence on the complex linear span of $s$. It holds on its generators by hypothesis, on zero because every functional sends zero to zero, and is preserved under addition and complex scalar multiplication by linearity and the corresponding rules for limits. Finally, the set of points where $L_m(x)$ converges to $M(x)$ is closed: it is the convergence set for an equicontinuous family with continuous target $M$. Since it contains the dense span, it is all of $E$, as required.
