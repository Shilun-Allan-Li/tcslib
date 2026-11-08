<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Expansion

**Claim.** Every function on $(\mathbb{Z}/k\mathbb{Z})^n$ equals the sum of its Fourier coefficients times the corresponding characters, evaluated at each vector.

**Proof.** 1. First establish dual orthogonality: for vectors $x,y$, the sum over all indices $s$ of $\chi_s(x-y)$ is $k^n$ when $x=y$ and zero otherwise. If $x=y$, every summand is $1$, and there are $k^n$ indices (`card_ZkVec`). If $x\ne y$, then $x-y\ne0$, so the mean of its character is zero (`expectation_char_nontrivial`); converting that mean to a sum shows the sum vanishes.
2. Next expand the Fourier coefficients in the proposed right-hand side as normalized sums over vectors $y$, and exchange the two finite summations. The character conjugation law (`char_s_conj`) and the addition law (`char_s_add`) combine the character factors into $\chi_s(x-y)$. Thus the inner sum over $s$ is precisely the dual-orthogonality sum just computed.
3. Dual orthogonality leaves only the term $y=x$, with factor $k^n$. The normalization in the Fourier coefficients cancels this factor, leaving $f(x)$, as claimed.

**Key facts.** `ZkFourier.card_ZkVec`, `ZkFourier.expectation_char_nontrivial`, `ZkFourier.char_s_conj`, `ZkFourier.char_s_add`.
