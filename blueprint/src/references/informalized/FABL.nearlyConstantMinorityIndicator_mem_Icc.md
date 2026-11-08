<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/NearlyConstantLevelOne.lean :: FABL.nearlyConstantMinorityIndicator_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of the minority indicator

**Claim.** For a Boolean function $f$ and sign vector $x$, the minority indicator of $f$ at $x$ lies in $[0,1]$.

**Proof.** Split according to whether the mean of $f$ is nonnegative. In either case, the value $f(x)$ is one of the two signs $1$ and $-1$. If the mean is nonnegative, the indicator is $(1-f(x))/2$, which is $0$ or $1$ according as $f(x)$ is $1$ or $-1$. If the mean is negative, it is $(1+f(x))/2$, again $0$ or $1$, in the opposite order. Thus in both cases the value belongs to $[0,1]$.
