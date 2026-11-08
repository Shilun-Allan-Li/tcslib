<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.spectralSparsity_ne_nine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Spectral Sparsity Avoids Nine

**Claim.** For every dimension $n$ and every function $f:\mathbb F_2^n\to\{\pm1\}$, the number of nonzero vector Fourier coefficients of its real-valued version is not $9$.

**Proof.** Assume for contradiction that the support has size $9$. The sign-valued granularity theorem (FABL.isVectorFourierGranular_signValue_spectralSparsity), together with the characterization of granularity as integer multiples (FABL.isVectorFourierGranular_iff), then shows that every Fourier coefficient is an integer multiple of the spacing. At sparsity $9$, the spacing is $1/4$, so write each coefficient as $z_\gamma/4$ with $z_\gamma\in\mathbb Z$. The support is the set of nonzero coefficients, and its cardinality is $9$ by (FABL.spectralSparsity_eq_card_vectorFourierSupport). Parseval's identity for sign-valued functions (FABL.sum_sq_vectorFourierCoeff_signValue_eq_one) says the sum of all squared coefficients is $1$. Coefficients outside the support vanish, so the sum over the support is also $1$. Substituting $z_\gamma/4$ and multiplying by $16$ gives $\sum_{\gamma\in\operatorname{supp}}z_\gamma^2=16$. Each multiplier on the support is a nonzero integer, hence its square is at least $1$. Fixing one support element, the other eight squares contribute at least $8$, so the fixed square is at most $8$. Thus every supported integer multiplier has square between $1$ and $8$. In particular, it is not divisible by $3$: a nonzero multiple of $3$ has square at least $9$. Therefore each $z_\gamma$ is nonzero modulo $3$, and its square is $1$ modulo $3$. Summing those squares modulo $3ootnote{The sum is finite, over the nine-element support.}$ gives $9$ modulo $3$, which is $0$, while the integer sum is $16$, which is $1$ modulo $3$. This contradiction rules out sparsity $9$.

**Key facts.** `FABL.isVectorFourierGranular_signValue_spectralSparsity`, `FABL.isVectorFourierGranular_iff`, `FABL.spectralSparsity_eq_card_vectorFourierSupport`, `FABL.sum_sq_vectorFourierCoeff_signValue_eq_one`, `FABL.mem_vectorFourierSupport`.
