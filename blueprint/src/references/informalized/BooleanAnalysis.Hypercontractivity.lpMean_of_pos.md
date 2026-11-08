<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.lpMean_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-Exponent Power Mean Formula

**Claim.** For $p>0$ and $f:\{0,1\}^n\to\mathbb R$, the extended power mean is $M_p(f)=(\mathbb E|f|^p)^{1/p}$, with expectation under the uniform measure.

**Proof.** Since $p>0$, the exceptional clauses in the definition of the extended mean do not apply: the zero-value clause requires $p\le0$, and the logarithmic clause requires $p=0$. Thus the definition reduces to the cube power norm, which is exactly $(\mathbb E|f|^p)^{1/p}$.
