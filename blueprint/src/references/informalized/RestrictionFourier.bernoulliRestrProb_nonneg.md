<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/FourierConcentration.lean :: RestrictionFourier.bernoulliRestrProb_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Restriction Probabilities

**Claim.** For $0\le p\le1$, the Bernoulli restriction probability of any decidable event on restrictions of $n$ variables is nonnegative.

**Proof.** The probability is a finite sum over restrictions. Each summand is the restriction weight multiplied by the event indicator. The restriction weight is nonnegative for $0\le p\le1$ (`SwitchingLemma.bernoulliRestrWeight_nonneg'`), and the indicator is either zero or one, hence nonnegative. Thus every summand, and therefore their sum, is nonnegative.

**Key facts.** `SwitchingLemma.bernoulliRestrWeight_nonneg'`.
