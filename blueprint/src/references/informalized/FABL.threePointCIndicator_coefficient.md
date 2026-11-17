<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.threePointCIndicator_coefficient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Fourier Coefficients

**Claim.** Against the specified three-point orthonormal basis under the uniform probability measure, the indicator of $c$ has coefficients $1/3$, $-\sqrt{2}/6$, and $-\sqrt{6}/6$ at indices $0$, $1$, and $2$, respectively.

**Proof.** First express the expectation under the uniform measure as the average over the three points. Reindex that average using the bijection from $\{0,1,2\}$ to $\{a,b,c\}$; the uniform-expectation identity is \texttt{pmfExpectation\_uniformPMF\_eq\_expect}. For each of the three indices, the indicator vanishes at $a$ and $b$ and equals $1$ at $c$, so the average reduces to one third of the basis function's value at $c$. Those values are $1$, $-\sqrt{2}/2$, and $-\sqrt{6}/2$, yielding the three claimed coefficients.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`.
