<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.hv_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halving the Logarithmic Width

**Claim.** For every nonzero natural number $k$, the function $h$, which is zero at zero and otherwise equals $\lfloor\log_2 k\rfloor+1$, satisfies $h(k)=h(\lfloor k/2\rfloor)+1$.

**Proof.** Unfold the definition of $h$ and split according to whether $k<2$. In the first case, nonzeroness forces $k=1$, so $k/2=0$ and both sides equal $1$. Otherwise $2\le k$, which implies $k/2\ne0$. Thus both values use their logarithmic branches, and the standard base-two logarithm identity for $1<2\le k$ gives $\log_2 k=\log_2(k/2)+1$. Adding the defining offset yields the desired equality.
