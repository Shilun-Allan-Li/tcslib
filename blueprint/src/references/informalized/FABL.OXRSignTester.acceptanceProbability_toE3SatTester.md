<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.OXRSignTester.acceptanceProbability_toE3SatTester -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability Conversion

**Claim.** For an OXR sign tester $T$ and bounded cube function $f$, the associated Max-E3-Sat tester has acceptance probability $1/2$ plus half the acceptance probability of the associated sign tester.

**Proof.** Fix a seed and let its three query values under $f$ be the three means. They lie in $[-1,1]$ by boundedness of $f$. Averaging the converted E3-Sat clause over a uniform sign $b$ gives one half plus one half the randomized value of the OXR predicate with the seed's selected inputs negated; this is the clause expectation identity (`expect_oxrE3SatClause_randomizedValue`). Now average over the original seed law. The expectation for the sequential sampling of a seed followed by a uniform sign is the iterated expectation (`pmfExpectation_bind`), and mapping the uniform sign into the clause evaluation simply rewrites the expectation as an average over signs (`pmfExpectation_map`). Substituting the fixed-seed identity yields the expectation of the constant $1/2$ plus one half the seedwise OXR randomized value. Linearity of expectation, the expectation of a constant, and extraction of a constant factor (`pmfExpectation_add`, `pmfExpectation_const`, and `pmfExpectation_const_mul`) give $1/2$ plus half the seed average. That seed average is precisely the sign tester's acceptance probability by its definition, proving the formula.

**Key facts.** `FABL.expect_oxrE3SatClause_randomizedValue`, `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`.
