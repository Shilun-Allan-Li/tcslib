<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.thresholdSign_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negating a Threshold Sign

**Claim.** For every nonzero real number $t$, the threshold sign of $-t$ is the negative of the threshold sign of $t$.

**Proof.** Because $t\ne0$, either $t<0$ or $t>0$. In the first case, $-t>0$, so its threshold sign is $1$, while that of $t$ is $-1$. In the second case, $-t<0$, so its threshold sign is $-1$, while that of $t$ is $1$. These values follow from the rules for negative and nonnegative inputs (`thresholdSign_of_neg` and `thresholdSign_of_nonneg`), and establish the identity in both cases.

**Key facts.** `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
