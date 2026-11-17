<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfExpectation_finiteBernoulli_zeroOne_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive powers of a Bernoulli bit

**Claim.** For a Bernoulli bit that equals $1$ with probability $q\in[0,1]$, the expectation of its $m$-th power is $q$ whenever $m$ is a positive natural number.

**Proof.** Because $m>0$, raising either possible bit value to the power $m$ leaves it unchanged: $0^m=0$ and $1^m=1$. Thus the powered function agrees pointwise with the bit itself. The expectation of the bit under this Bernoulli distribution is $q$ (\texttt{FABL.pmfExpectation_pBiasedBitPMF_zeroOneValue}), so the powered function has the same expectation.

**Key facts.** `FABL.pmfExpectation_pBiasedBitPMF_zeroOneValue`.
