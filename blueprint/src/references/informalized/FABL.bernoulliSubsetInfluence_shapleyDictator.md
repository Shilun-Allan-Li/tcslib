<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.bernoulliSubsetInfluence_shapleyDictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator Subset Influence

**Claim.** For every real parameter $p$, the Bernoulli subset influence of the singleton dictator at its sole coordinate is $p(1-p)$.

**Proof.** The identity relating influence to marginal contribution applies because the singleton dictator is monotone and takes only the values zero and one (\texttt{shapleyDictator\_monotone}, \texttt{shapleyDictator\_zeroOne}). Its marginal contribution is $1$ by the singleton calculation (\texttt{bernoulliMarginalContribution\_shapleyDictator}). Substitution into the identity gives $p(1-p)\cdot 1=p(1-p)$.

**Key facts.** `FABL.bernoulliSubsetInfluence_eq_mul_marginalContribution`, `FABL.shapleyDictator_monotone`, `FABL.shapleyDictator_zeroOne`, `FABL.bernoulliMarginalContribution_shapleyDictator`.
