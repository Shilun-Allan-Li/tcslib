<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EdgeIsoperimetric.lean :: FABL.two_mul_min_mul_log_two_le_binEntropy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary entropy lower bound

**Claim.** For every real number $p$ with $0\le p\le1$, $2\min(p,1-p)\log 2\le H(p)$, where $H$ is the binary entropy.

**Proof.** Split according to whether $p\le\tfrac12$. In that case, $\min(p,1-p)=p$, and the half-interval estimate $2p\log 2\le H(p)$ applies (\texttt{FABL.two_mul_mul_log_two_le_binEntropy_of_le_half}). If $p>\tfrac12$, put $q=1-p$. Then $0\le q<\tfrac12$, so the same estimate gives $2q\log 2\le H(q)$. Binary entropy is symmetric under complementation, $H(1-p)=H(p)$, and here $q=\min(p,1-p)$. This proves the desired bound in the second case as well.

**Key facts.** `FABL.two_mul_mul_log_two_le_binEntropy_of_le_half`.
