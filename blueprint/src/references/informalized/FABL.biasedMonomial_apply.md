<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedMonomial_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Monomial Formula

**Claim.** For $p\in(0,1)$, a coordinate set $S$, and an input $x$, the biased monomial indexed by $S$ is the product over $i\in S$ of the standardized biased sign at coordinate $i$.

**Proof.** Expand the biased monomial as the product over all coordinates of the corresponding one-site basis function, using the subset index that assigns the nonconstant basis index precisely on $S$. The basis evaluation identity (\texttt{FABL.biasedSiteBasis_apply}) identifies each basis vector with its defining one-site Fourier function. For coordinates in $S$ this function is the standardized biased sign; outside $S$ it is the constant $1$. Thus the full product reduces to the product over $S$, as claimed.

**Key facts.** `FABL.biasedSiteBasis_apply`.
