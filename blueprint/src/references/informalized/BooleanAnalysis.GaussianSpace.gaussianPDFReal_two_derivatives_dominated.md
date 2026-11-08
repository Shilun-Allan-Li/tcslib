<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.gaussianPDFReal_two_derivatives_dominated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Common Gaussian derivative envelope

**Claim.** For positive variance $v$ and $M\ge0$, there is a nonnegative integrable function that simultaneously bounds the Gaussian density and its first and second mean derivatives in the stated forms, uniformly for $|m|\le M$.

**Proof.** Apply the first-derivative envelope lemma (\texttt{gaussianPDFReal\_meanDerivative\_dominated}) and the second-derivative envelope lemma (\texttt{gaussianPDFReal\_secondMeanDerivative\_dominated}), obtaining integrable bounds $b_1$ and $b_2$. Each is nonnegative: use its bound at mean $m=0$, which is allowed since $M\ge0$. Define $b(z)=p_v(0,z)+(M+1)b_1(z)+b_2(z)$. This function is integrable, and its terms are nonnegative. To bound the density at mean $m$, use the mean value estimate on the interval from $0$ to $m$: the derivative of the density with respect to its mean is $(z-a)p_v(a,z)/v$ (\texttt{hasDerivAt\_gaussianPDFReal\_mean}), whose absolute value on that interval is at most $b_1(z)$. Since $|m|\le M$, this gives $p_v(m,z)\le p_v(0,z)+Mb_1(z)$. The first-derivative quantity is bounded by $b_1(z)$, and the second-derivative quantity by $b_2(z)$. Nonnegativity of the summands and $M+1\ge1$ show that all three are bounded by $b(z)$.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianPDFReal_meanDerivative_dominated`, `BooleanAnalysis.GaussianSpace.gaussianPDFReal_secondMeanDerivative_dominated`, `BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianPDFReal_mean`.
