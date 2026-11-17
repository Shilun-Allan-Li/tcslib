<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.polynomialThresholdRepresentation_isThresholdOfThresholds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Composition Representation

**Claim.** Let $n$ be a natural number, let $f:\{−1,1\}^n\to\{−1,1\}$, and let $p:\{−1,1\}^n\to\mathbb R$. Suppose $f(x)=1$ when $p(x)\geq0$ and $f(x)=-1$ when $p(x)<0$. Then $f$ is a threshold of $(2n)s$ linear threshold functions, where $s$ is the number of nonzero Fourier coefficients of $p$ on the Boolean cube.

**Proof.** Let $\mathcal S$ be the Fourier support of $p$. For each $S\in\mathcal S$, the parity function on $S$ is a function of the number of positive coordinates in $S$. The profile decomposition expresses that profile as a constant sign plus a sum of $2n$ gates, each a linear threshold function (\texttt{FABL.profileDecompositionGates_isLinearThreshold} and \texttt{FABL.sum_profileDecompositionGates}). Consequently, the parity monomial for $S$ is the sum of that constant sign and those $2n$ gate outputs. Weight the gates for $S$ by the Fourier coefficient of $p$ at $S$, and combine the constants into one overall offset. Indexing all pairs consisting of a support element and one of its $2n$ gates gives $s(2n)$ gates; reindexing this finite family does not change the weighted sum. For every input, the resulting affine combination equals the Fourier expansion of $p$, since the Fourier expansion over its support recovers $p$ (\texttt{FABL.fourier_expansion_over_support}). Thresholding this combination therefore gives the same output as thresholding $p$, namely $f$.

**Key facts.** `FABL.profileDecompositionGates_isLinearThreshold`, `FABL.sum_profileDecompositionGates`, `FABL.parityFunction_eq_parityCountProfile`, `FABL.parityFunction_toReal`, `FABL.fourier_expansion_over_support`.
