<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/DNF.lean :: BooleanAnalysis.Hypercontractivity.dnf_fourierWeightAbove_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Weight Tail for DNFs

**Claim.** For a DNF of width at most $w$, with no repeated variable within a term and no repeated literal in a term, its Boolean sign function has Fourier weight above degree $120w(t+1)$ at most $8(1/2)^t$.

**Proof.** Set $K=120w(t+1)$. If $n\le K$, every subset of the $n$ coordinates has size at most $K$, so the Fourier weight above $K$ is zero and the bound follows.

Now suppose $n>K$. Choose the restriction probability $p=1/(40w)$. It is positive and at most $1$. Whenever a subset $S$ has $|S|>K$, the choice of $K$ implies $3(t+1)\le p|S|$. Therefore the Fourier tail above $K$ is bounded term by term by the Fourier sum over subsets satisfying this latter threshold condition.

The restriction-to-Fourier estimate (`RestrictionFourier.odonnell_lemma_4_21`) bounds that sum by four times the probability that a random restriction leaves decision-tree depth at least $t+1$. The DNF switching lemma (`SwitchingBernoulli.switching_bernoulli_dtDepth_dnf`) bounds this probability by $(1/2)^t+\exp(-np/3)$. Since $n>K$, the cutoff inequality also gives $np/3\ge t+1$, so $\exp(-np/3)\le \exp(-t)$. Finally, $\exp(-1)\le1/2$, hence $\exp(-t)\le(1/2)^t$. Combining the estimates gives at most $4((1/2)^t+(1/2)^t)=8(1/2)^t$.

**Key facts.** `RestrictionFourier.odonnell_lemma_4_21`, `SwitchingBernoulli.switching_bernoulli_dtDepth_dnf`.
