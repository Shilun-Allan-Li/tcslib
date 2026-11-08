<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.IsFourierSpectrumConcentratedOn.transfer_of_uniformLpNorm_sub_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transfer of Fourier Concentration

**Claim.** If the squared Fourier coefficients of $f$ outside a family $\mathcal F$ sum to at most $\varepsilon_1$, and the squared uniform $L^2$ norm of $f-g$ is at most $\varepsilon_2$, then the squared Fourier coefficients of $g$ outside $\mathcal F$ sum to at most $2(\varepsilon_1+\varepsilon_2)$.

**Proof.** Let $r=f-g$. Parseval's identity together with the identity equating the squared uniform $L^2$ norm to the uniform inner product (\texttt{uniformLpNorm_two_sq_eq_uniformInner}, \texttt{parseval}) shows that the sum of $r$'s squared Fourier coefficients over all frequencies is at most $\varepsilon_2$. In particular, the sum over frequencies outside $\mathcal F$ is at most this total, since each summand is a square and hence nonnegative. For each frequency $S$, linearity of Fourier coefficients under subtraction (\texttt{fourierCoeff_sub}) gives $\widehat g(S)=\widehat f(S)-\widehat r(S)$. The elementary inequality $(u-v)^2\le 2u^2+2v^2$ then bounds $\widehat g(S)^2$ by twice the sum of the corresponding squares for $f$ and $r$. Summing this inequality outside $\mathcal F$ and applying the two assumed bounds yields $2\varepsilon_1+2\varepsilon_2=2(\varepsilon_1+\varepsilon_2)$.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.parseval`, `FABL.fourierCoeff_sub`.
