<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/KikuchiLDC/LDC/HighValue.lean :: high_value_observation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Large Value Assignment

**Claim.** There exist assignments of signs to the message and coordinate variables for which the defined polynomial is at least $2\epsilon$.

**Proof.** Choose every message sign and every coordinate sign to be $1$. These are valid signs. Every constraint product is then $1$, so the polynomial's numerator is the sum of the sizes of all matchings, namely the total number of constraints. The hypothesis that this total is positive permits cancellation with its reciprocal normalization, leaving value $1$. Since $\epsilon\le 1/2$, this is at least $2\epsilon$.

**Caveat.** The supplied informal statement describes an expected-value bound for a different formulation; the formal theorem and its proof establish the stated existential assignment result.
