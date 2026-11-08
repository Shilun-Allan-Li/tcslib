<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdBias.lean :: FABL.thresholdPair_nonpos_of_bias_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative bias gives a nonpositive threshold pair

**Claim.** If $a_0<0$, then for every real $t$ the threshold signs of $a_0+t$ and $a_0-t$ have nonpositive sum.

**Proof.** Each threshold sign has real value $1$ for a nonnegative input and $-1$ for a negative input (`signValue_thresholdSign`). The two inputs cannot both be nonnegative, since their sum is $2a_0<0$. If both are negative, the sum of their signs is $-2$; if exactly one is nonnegative, that sum is $0$. In either possible case it is nonpositive.

**Key facts.** `FABL.signValue_thresholdSign`.
