<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdInfluence.lean :: FABL.thresholdSign_add_ne_sub_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# When sum and difference thresholds differ

**Claim.** For real $r,a$, the threshold signs of $r+a$ and $r-a$ differ exactly when $-|a|\le r<|a|$.

**Proof.** Split according to the sign of $a$. If $a\ge0$, then $|a|=a$. The interval condition says $r+a\ge0$ and $r-a<0$, so the two threshold signs are $1$ and $-1$. Conversely, if the signs differ, the only possible ordering is that $r+a$ is nonnegative and $r-a$ is negative: the reverse ordering would require both $r+a<0$ and $r-a\ge0$, impossible for $a\ge0$. These two inequalities give $-a\le r<a$. If $a<0$, then $|a|=-a$; the interval condition instead gives $r+a<0$ and $r-a\ge0$, hence different signs. Conversely, the reverse ordering is now impossible, and differing signs force precisely those inequalities, equivalent to $a\le r<-a$. In both cases we use that the threshold sign is $1$ on nonnegative inputs and $-1$ on negative inputs (`thresholdSign_of_nonneg`, `thresholdSign_of_neg`); the strict upper endpoint reflects that zero has positive threshold sign.

**Key facts.** `FABL.thresholdSign_of_neg`, `FABL.thresholdSign_of_nonneg`.
