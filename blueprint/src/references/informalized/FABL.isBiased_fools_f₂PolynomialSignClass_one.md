<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/Viola.lean :: FABL.isBiased_fools_f₂PolynomialSignClass_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small bias fools affine sign functions

**Claim.** If a probability density has Fourier bias at most $\varepsilon$ on every nonzero frequency, where $\varepsilon\ge 0$, then it $\varepsilon$-fools the sign encodings of Boolean functions of algebraic degree at most one.

**Proof.** Take a function in the class. Every Boolean function of degree at most one is affine, so write it as an affine function with constant term $b$ and linear frequency $a$ (`exists_affineFunction_of_functionAlgebraicDegree_le_one`). Its real sign encoding is the affine sign function, namely the constant sign $\operatorname{signValue}(\operatorname{signEncode}(b))$ times the Walsh character at $a` (`realSignEncodedFunction_affineFunction`, `affineSignFunction_apply`). If $a=0$, this is constant. The density expectation of the constant sign equals its uniform expectation because the density has expectation one (`ProbabilityDensity.expect_eq_one`), so the difference is zero and is at most $\varepsilon$. If $a\ne0$, the Walsh character has uniform expectation zero (`expect_vectorWalshCharacter`). Factoring the constant sign out of both expectations shows that the absolute difference between the density and uniform expectations is the absolute value of the density's expectation against this character; the constant sign has absolute value one (`signValue_eq_neg_one_or_one`). By the Fourier-coefficient expectation formula, that density expectation is the Fourier coefficient at $a` (`vectorFourierCoeff_eq_expect`), whose absolute value is at most $\varepsilon$ by the assumed bias bound. This proves the required fooling inequality in both cases.

**Key facts.** `FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one`, `FABL.realSignEncodedFunction_affineFunction`, `FABL.affineSignFunction_apply`, `FABL.ProbabilityDensity.expect_eq_one`, `FABL.expect_vectorWalshCharacter`, `FABL.signValue_eq_neg_one_or_one`, `FABL.vectorFourierCoeff_eq_expect`.
