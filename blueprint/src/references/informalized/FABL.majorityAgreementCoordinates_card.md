<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.majorityAgreementCoordinates_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority agreement coordinate bound

**Claim.** If $d$ is odd and positive and $x\in\{−1,1\}^d$, then strictly more than half the coordinates of $x$ equal its majority sign; equivalently, $d<2$ times the number of agreement coordinates.

**Proof.** Let $s=\sum_i x_i$, interpreting each sign as the real number $\pm1$. The sum is nonzero for odd $d$ (FABL.sum_signValue_ne_zero_of_odd), so split into the cases $s\ge0$ and $s<0$. If $s\ge0$, then in fact $s>0$, and the majority sign is $1$ by the threshold-sign rule (FABL.thresholdSign_of_nonneg). Thus the agreement coordinates are exactly the positive coordinates. The identity $s=2P-d$, where $P$ is the number of positive coordinates (FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub), now gives $d<2P$, as required. If $s<0$, the majority sign is $-1$ by the negative threshold-sign rule (FABL.thresholdSign_of_neg). The agreement coordinates are then exactly the nonpositive coordinates, so their count is $d-P$. The same identity and $s<0$ imply $2P<d$; hence $d<2(d-P)$, which is the desired bound in this case as well.

**Key facts.** `FABL.sum_signValue_ne_zero_of_odd`, `FABL.thresholdSign_of_nonneg`, `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`, `FABL.thresholdSign_of_neg`.
