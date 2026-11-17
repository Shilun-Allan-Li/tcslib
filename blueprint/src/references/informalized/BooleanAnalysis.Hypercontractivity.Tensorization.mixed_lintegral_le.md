<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.Tensorization.mixed_lintegral_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison of Mixed Nonnegative Integrals

**Claim.** For measurable nonnegative $g$ on a product of probability spaces and real exponents $0<p\le q$, the mixed $L^p$-then-$L^q$ expression is at most the mixed $L^q$-then-$L^p$ expression.

**Proof.** Set $r=q/p$, so $r\ge1$, and apply Minkowski's inequality for product integrals (lintegral_minkowski) to the function $(x,y)\mapsto g(x,y)^p$ and exponent $r$. This gives
\[\left(\int_B\left(\int_A g(x,y)^p\,d\mu(x)\right)^{q/p}d\nu(y)\right)^{p/q}\le \int_A\left(\int_B g(x,y)^q\,d\nu(y)\right)^{p/q}d\mu(x).\]
Here the right side uses $pr=q$. Raise both sides to the nonnegative power $1/p$; monotonicity of powers preserves the inequality and yields the claimed comparison.

**Key facts.** `BooleanAnalysis.Hypercontractivity.Tensorization.lintegral_minkowski`.
