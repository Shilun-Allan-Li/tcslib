<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdInfluence.lean :: FABL.mul_signValue_thresholdSign_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold sign multiplication identity

**Claim.** For $a\in\mathbb R$ and $s\in\{-1,1\}$, the product $a\,\operatorname{sign}(a)s$ equals $|a|s$, with the sign convention that zero has sign $1$.

**Proof.** If $a\ge0$, its threshold sign is $1$ and $|a|=a$, so the identity follows directly. If $a<0$, its threshold sign is $-1$ and $|a|=-a$. Since $s$ is either $1$ or $-1$, substituting either value gives $a(-1)s=(-a)s=|a|s$. The threshold-sign evaluations in these two cases are the facts that the sign is $1$ on nonnegative inputs (\texttt{FABL.thresholdSign\_of\_nonneg}) and $-1$ on negative inputs (\texttt{FABL.thresholdSign\_of\_neg}).

**Key facts.** `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
