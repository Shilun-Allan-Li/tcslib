<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EdgeIsoperimetric.lean :: FABL.two_mul_mul_log_two_le_binEntropy_of_le_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary entropy bound on half interval

**Claim.** For every real number $p$ with $0\le p\le\tfrac12$, the binary entropy satisfies $2p\log 2\le H(p)$, with its continuous endpoint convention.

**Proof.** Write $1=(1-2p)+2p$, where both coefficients are nonnegative. Concavity of binary entropy on $[0,1]$, applied to the convex combination of $0$ and $\tfrac12$ with weights $1-2p$ and $2p$, gives $H(p)\ge(1-2p)H(0)+2pH(\tfrac12)$. Since $H(0)=0$ and $H(\tfrac12)=\log 2$, the right-hand side is $2p\log 2$, as required.
