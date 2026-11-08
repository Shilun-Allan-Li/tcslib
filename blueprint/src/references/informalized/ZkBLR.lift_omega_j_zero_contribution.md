<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.lift_omega_j_zero_contribution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-twisted lift contribution

**Claim.** For every function $f$, the sum over frequencies of the squared moduli of the Fourier coefficients of its zero-twisted lift, weighted by the real parts of those coefficients, is $1$.

**Proof.** The zero-twisted lift is the constant function $1$. For each nonzero frequency $s$, its Fourier coefficient is the expectation of the complex conjugate of the character at $s$. Conjugation changes that character to the one at $-s$ (\texttt{ZkFourier.char\_s\_conj}); since $s\ne0$ implies $-s\ne0$, the expectation of this nontrivial character vanishes (\texttt{ZkFourier.expectation\_char\_nontrivial}). Thus every nonzero-frequency summand is zero. At frequency zero the coefficient is the expectation of the constant function $1$, hence equals $1$: the vector space has $k^n$ elements (\texttt{ZkFourier.card\_ZkVec}), matching the normalization denominator, and the lifted value at zero is $1$ (\texttt{ZkFourier.toOmega\_zero}). Its contribution is therefore $|1|^2\operatorname{Re}(1)=1$, proving the identity.

**Key facts.** `ZkFourier.char_s_conj`, `ZkFourier.expectation_char_nontrivial`, `ZkFourier.card_ZkVec`, `ZkFourier.toOmega_zero`.
