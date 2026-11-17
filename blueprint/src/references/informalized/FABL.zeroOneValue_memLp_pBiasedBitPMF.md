<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.zeroOneValue_memLp_pBiasedBitPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square Integrability of a Biased Bit

**Claim.** For every $p\in[0,1]$, the function on a Boolean bit that is $1$ on true and $0$ on false belongs to $L^2$ for the probability measure assigning mass $p$ to true and $1-p$ to false.

**Proof.** The function is measurable because the Boolean domain is finite. Its absolute value is at most $1$ at every point: it is $1$ at true and $0$ at false. A bounded measurable function on this probability space is in $L^2$, giving the result.
