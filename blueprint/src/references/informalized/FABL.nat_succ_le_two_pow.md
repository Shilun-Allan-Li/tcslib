<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.nat_succ_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor bounded by a power of two

**Claim.** For every natural number $m$, one has $m+1\le 2^m$.

**Proof.** Proceed by induction on $m$. At $m=0$, both sides are $1$. For the induction step, the hypothesis is $m+1\le 2^m$. The right-hand side at the next index is $2^{m+1}=2^m\cdot2$. This is at least $(m+1)+1$, since $2^m\ge1$ and hence $2^m\cdot2\ge 2^m+1\ge m+2$. Thus the desired inequality holds at $m+1$.
