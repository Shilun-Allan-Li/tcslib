<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/IntegralThresholdRepresentations.lean :: FABL.thresholdSign_eq_neg_one_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative threshold sign forces negative input

**Claim.** For every real $t$, if its threshold sign is $-1$, then $t<0$.

**Proof.** Suppose instead that $t\ge0$. The threshold sign is then $1$ (`thresholdSign_of_nonneg`), contradicting the assumption that it is $-1$. Hence $t<0$.

**Key facts.** `FABL.thresholdSign_of_nonneg`.
