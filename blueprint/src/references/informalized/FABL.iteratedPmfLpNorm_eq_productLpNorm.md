<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.iteratedPmfLpNorm_eq_productLpNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated and product $L^p$ norms

**Claim.** For $p>0$, the iterated $L^p$ norm of $f$ with respect to $\lambda$ in each coordinate equals its $L^p$ norm under the product law on $\Omega^n$.

**Proof.** Induct on the number of coordinates. When $n=0$, the product law is concentrated on the empty tuple (`productProbabilityPMF_zero`), so its expectation evaluates the integrand there (`pmfExpectation_pure`). The iterated norm is the absolute value of the same function value (`iteratedPmfLpNorm_zero`). The equality then follows from the laws $a=a^{p p^{-1}}$ for $a\ge 0$ and $(a^p)^{p^{-1}}=a^{p p^{-1}}$, using $p>0$. For the successor step, write the iterated norm as the one-coordinate norm of the norms on the first $n$ coordinates (`iteratedPmfLpNorm_succ`), and use the induction hypothesis inside that expression. The product-law expectation also decomposes into an outer expectation over the last coordinate and an inner expectation over the first $n$ (`pmfExpectation_productProbabilityPMF_succ`). The identity $|\|h\|_p|^p=\mathbb E|h|^p$ for a finite probability law (`pmfLpNorm_rpow`) identifies the inner expressions, yielding the desired equality.

**Key facts.** `FABL.iteratedPmfLpNorm_zero`, `FABL.productProbabilityPMF_zero`, `FABL.pmfExpectation_pure`, `FABL.iteratedPmfLpNorm_succ`, `FABL.pmfExpectation_productProbabilityPMF_succ`, `FABL.pmfLpNorm_rpow`.
