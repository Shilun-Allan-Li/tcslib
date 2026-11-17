<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.switchingLayerRate_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative switching layer rate

**Claim.** For every natural number $w$, the switching layer rate $1/(10w)$ is nonnegative.

**Proof.** The denominator is the product of $10$, which is positive, and the real cast of $w$, which is nonnegative. The reciprocal of a nonnegative denominator is nonnegative under the reciprocal convention used here, so $1/(10w)\ge0$.
