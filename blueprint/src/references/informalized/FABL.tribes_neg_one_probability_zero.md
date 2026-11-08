<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribes_neg_one_probability_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-block negative probability

**Claim.** For every $w$, the uniform probability that tribes with zero blocks takes value $-1$ equals $1-(1-2^{-w})^0$.

**Proof.** With zero blocks, tribes is the constant function $+1$ (`FABL.tribes_zero`). Thus the event that its value is $-1$ is empty, and its uniform probability is zero. The displayed expression is also zero because $(1-2^{-w})^0=1$.

**Key facts.** `FABL.tribes_zero`.
