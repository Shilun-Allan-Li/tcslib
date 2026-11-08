<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.bernoulliSubsetInfluence_eq_mul_marginalContribution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence and Marginal Contribution

**Claim.** For a monotone, zero-one-valued function on subsets, the Bernoulli subset influence at each coordinate equals $p(1-p)$ times its Bernoulli marginal contribution.

**Proof.** Expand the definitions of influence and marginal contribution. In each summand indexed by a subset $S$, the same Bernoulli weight multiplies either the square of the marginal difference or the marginal difference itself. Monotonicity and the zero-one range imply that this difference is either $0$ or $1$; hence its square equals itself (\texttt{sq\_subsetMarginal\_eq\_self}). The summands, and therefore their sums, agree. The common expectation is multiplied by $p(1-p)$ in the definition of influence, giving the result.

**Key facts.** `FABL.sq_subsetMarginal_eq_self`.
