<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.expect_oxrE3SatReplacementClauses -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected acceptance of a random clause

**Claim.** For fixed $\sigma$ and input triple $v$, the expected acceptance indicator of the clause whose falsifying signs are formed from $(1,b,b)$ is one half plus half the acceptance indicator of the OXR predicate applied to the inputs negated according to $\sigma$.

**Proof.** The random sign $b$ is uniform on $\{\pm1\}$, so its expectation is the average of the acceptance indicators for $b=1$ and $b=-1$ (`expect_sign`). For fixed input signs, each of the three coordinates has one of two possible values; splitting into these cases and into whether each coordinate is negated by $\sigma$ reduces the assertion to checking the two clause outcomes against the OXR acceptance condition. In that finite check, if the negated inputs satisfy OXR, exactly one of the two clauses accepts, giving average $1/2$; if they do not, both accept, giving average $1$. These are precisely one half plus half the OXR acceptance indicator.

**Key facts.** `FABL.expect_sign`.
