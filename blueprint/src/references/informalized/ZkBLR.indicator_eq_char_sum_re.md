<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.indicator_eq_char_sum_re -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator as a character sum

**Claim.** The indicator of $a=0$ equals $1/k$ times the real part of the sum of the characters $\omega_k^{ja}$ over all $j\in\mathbb Z/k\mathbb Z$.

**Proof.** Apply the dual geometric-sum identity: the complex sum is $k$ when $a=0$ and $0$ otherwise (\texttt{ZkBLR.geom\_sum\_toOmega\_dual}). In the first case its real part is $k$, so multiplication by $1/k$ gives $1$; in the second case the result is $0$. These are exactly the two values of the indicator.

**Key facts.** `ZkBLR.geom_sum_toOmega_dual`.
