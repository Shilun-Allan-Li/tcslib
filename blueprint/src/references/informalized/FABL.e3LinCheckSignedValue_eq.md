<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadLimitations.lean :: FABL.e3LinCheckSignedValue_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed value of a linearity check

**Claim.** For a three-query check accepting exactly when the product of its queried signs equals $b$, its signed value on a Boolean function is $b$ times the product of the function's three queried values.

**Proof.** The predicate has the form of the three-variable linearity test with right-hand side $b$. Its randomized acceptance probability at input means $\mu_0,\mu_1,\mu_2$ is $(1+b\mu_0\mu_1\mu_2)/2$ (`FABL.e3LinPredicate_randomizedValue`). For the Boolean function, these means are its real-valued outputs at the three queries. The signed value is twice this acceptance probability minus one, so it simplifies to $b$ times the product of those outputs, as claimed.

**Key facts.** `FABL.e3LinPredicate_randomizedValue`.
