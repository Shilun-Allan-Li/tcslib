<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Bernstein.lean :: ProbabilityTheory.HasBernsteinMGF.measure_le_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bernstein tail bound

**Claim.** If a random variable has a Bernstein moment-generating-function bound with parameters $c$ and $t_{\rm max}$, then for $0\le s\le 2ct_{\rm max}$ its lower tail is at most $\exp(-s^2/(4c))$.

**Proof.** Choose $t=-s/(2c)$, which lies in $[-t_{\rm max},0]$ by the assumed range of $s$. The lower-tail Chernoff inequality gives $\mu\{X\le -s\}\le e^{-t(-s)}\,\operatorname{mgf}(X,\mu,t)$. The moment-generating-function hypothesis bounds this by $\exp(-t(-s)+ct^2)$. Substitution of the chosen negative parameter simplifies the exponent to $-s^2/(4c)$, proving the claim.
