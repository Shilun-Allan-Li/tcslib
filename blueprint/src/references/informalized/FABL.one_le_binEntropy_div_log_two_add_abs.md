<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EdgeIsoperimetric.lean :: FABL.one_le_binEntropy_div_log_two_add_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary entropy and distance from balance

**Claim.** For $0\le p\le1$, binary entropy obeys $1\le H(p)/\log 2+|2p-1|$.

**Proof.** Since $\log 2>0$, rearranging the claim reduces it to a lower bound on the entropy by $\log 2$ times $1-|2p-1|$. The entropy estimate $2\min(p,1-p)\log 2\le H(p)$ supplies this bound (`two_mul_min_mul_log_two_le_binEntropy`): when $p\le1/2$, the minimum is $p$ and $|2p-1|=1-2p$; when $p>1/2$, the minimum is $1-p$ and $|2p-1|=2p-1$. In each case the right-hand entropy lower bound is exactly $\log 2(1-|2p-1|)$, proving the inequality.

**Key facts.** `FABL.two_mul_min_mul_log_two_le_binEntropy`.
