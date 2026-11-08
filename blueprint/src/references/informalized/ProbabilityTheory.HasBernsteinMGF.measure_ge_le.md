<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Bernstein.lean :: ProbabilityTheory.HasBernsteinMGF.measure_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bernstein tail bound

**Claim.** If a random variable has a Bernstein moment-generating-function bound with parameters $c$ and $t_{m max}$, then for $0\le s\le 2ct_{\rm max}$ its upper tail is at most $\exp(-s^2/(4c))$.

**Proof.** Choose the Chernoff parameter $t=s/(2c)$. Since $c>0$ and $s\le 2ct_{\rm max}$, this choice lies in $[0,t_{\rm max}]$, so the exponential is integrable and the assumed moment-generating-function bound applies. Chernoff's inequality gives $\mu\{s\le X\}\le e^{-ts}\,\operatorname{mgf}(X,\mu,t)$. Using the assumed bound, the right-hand side is at most $\exp(-ts+ct^2)$. Substituting $t=s/(2c)$ makes this exponent $-s^2/(4c)$, as required.
