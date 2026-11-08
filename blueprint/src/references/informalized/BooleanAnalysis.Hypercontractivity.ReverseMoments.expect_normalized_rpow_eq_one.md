<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Holder.lean :: BooleanAnalysis.Hypercontractivity.ReverseMoments.expect_normalized_rpow_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalization of a power moment

**Claim.** For nonzero $r$, a pointwise nonnegative function $u$ with positive moment $E=\mathbb E[u^r]$ satisfies $\mathbb E[(u/E^{1/r})^r]=1$.

**Proof.** Write $E=\mathbb E[u^r]$. Since $E>0$, real-power laws give $(E^{1/r})^r=E$. Pointwise nonnegativity of $u$ permits the quotient power rule, so $(u/E^{1/r})^r=u^r/E$. Averaging this identity factors the constant denominator out of the finite sum defining expectation. The result is $\mathbb E[u^r]/E=E/E=1$.
