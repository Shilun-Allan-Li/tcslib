<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorRegularity.lean :: BooleanAnalysis.GaussianSpace.lipschitzWith_comp_contraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz continuity under contraction

**Claim.** If $D$ is Lipschitz with constant $C$ and $L$ is a continuous linear map of operator norm at most $1$, then $x\mapsto D(Lx)\circ L$ is Lipschitz with constant $C$.

**Proof.** For $x,y$, the difference of the resulting functionals is $(D(Lx)-D(Ly))\circ L$. Its norm is at most $\|D(Lx)-D(Ly)\|\,\|L\|$, hence at most $\|D(Lx)-D(Ly)\|$. By the Lipschitz bound for $D$, this is at most $C\|Lx-Ly\|$. The operator norm bound on $L$ gives $\|Lx-Ly\|\le\|x-y\|$, yielding the claimed estimate.
