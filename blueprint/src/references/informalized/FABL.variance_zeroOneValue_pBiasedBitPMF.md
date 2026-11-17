<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.variance_zeroOneValue_pBiasedBitPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Biased Bit

**Claim.** For a bit whose value is $1$ with probability $p$ and $0$ with probability $1-p$, where $p\in[0,1]$, the variance of its zero-one value is $p(1-p)$.

**Proof.** The zero-one value squares to itself, since each possible value is either $0$ or $1$. Its expectation is $p$ (`integral_zeroOneValue_pBiasedBitPMF`). The variance identity for a square-integrable random variable expresses the variance as the second moment minus the square of the mean; square integrability is supplied by `zeroOneValue_memLp_pBiasedBitPMF`. Thus the variance is $p-p^2=p(1-p)$.

**Key facts.** `FABL.zeroOneValue_memLp_pBiasedBitPMF`, `FABL.integral_zeroOneValue_pBiasedBitPMF`.
