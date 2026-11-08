<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.expect_oxrE3SatClause_randomizedValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized signed clause value

**Claim.** Averaging the randomized value of the clause whose falsifying signs are formed from $(1,b,b)$, with the sign changes prescribed by $\sigma$, gives one half plus one half the randomized value of the OXR predicate with inputs negated according to $\sigma$.

**Proof.** First average over the random sign $b$. Its two equally likely values, $1$ and $-1$, turn the average into the mean of the two corresponding clause values (`expect_sign`). For each fixed triple of inputs, the average of the two clause acceptance indicators is one half plus half the acceptance indicator of the negated-input OXR predicate (`expect_oxrE3SatReplacementClauses`). Hence the sum of those two indicator functions is pointwise $1$ plus that predicate's indicator. Averaging this identity over the product distribution of the three randomized signs turns the average of the sum into the sum of the averages (`pmfExpectation_add`); the constant term averages to $1$ (`pmfExpectation_const`). Dividing by two gives the claimed identity.

**Key facts.** `FABL.expect_sign`, `FABL.expect_oxrE3SatReplacementClauses`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`.
