<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.IsHypercontractive.conjugate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjugate Exponent Hypercontractivity

**Claim.** If the variable is hypercontractive from exponent $2$ to $q>2$ with parameter $\rho$ and has mean zero, then it is hypercontractive from the conjugate exponent $q/(q-1)$ to $2$ with the same parameter.

**Proof.** Set $p=q/(q-1)$, so $1\le p\le2$. The original integrability at exponent $q$ implies $X\in L^2$; consequently, the affine functions used below lie in the required spaces. Fix $a,b$ and write $f=a+bX$, $Z=a+\rho bX$, and $g=a+\rho^2bX$. The original contraction, applied with coefficients $a,\rho b$, gives $\|g\|_q\le\|Z\|_2$. The zero-mean assumption also gives $\int fg=\int |Z|^2=\|Z\|_2^2$: expanding the two products shows their difference is a constant multiple of $X$, whose integral vanishes. By the integral bound for a product and Hölder with conjugate exponents $p,q$, we have $\|Z\|_2^2=|\int fg|\le\|f\|_p\|g\|_q\le\|f\|_p\|Z\|_2$. Translating this estimate from extended norms to their real-valued versions yields $\|Z\|_2^2\le\|f\|_p\|Z\|_2$. If $\|Z\|_2=0$, the desired inequality is immediate; otherwise divide by this positive norm to obtain $\|a+\rho bX\|_2\le\|a+bX\|_p$. Together with the exponent, parameter, and integrability conditions inherited or established above, this is the claimed conjugate-exponent hypercontractivity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.rvLpNorm_rpow`.
