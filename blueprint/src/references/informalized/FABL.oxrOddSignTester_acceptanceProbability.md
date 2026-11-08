<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oxrOddSignTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Tester Acceptance Identity

**Claim.** The odd OXR tester’s acceptance probability on $f$ equals the ordinary three-query OXR acceptance probability on the odd part of $f$.

**Proof.** Condition first on the sampled three-query instance. The tester then chooses three independent uniform sign flips and applies them to the queries before evaluating the predicate. Averaging over these flips is exactly the odd-symmetrized value of that query check. The odd-symmetrization identity says this value equals the check’s ordinary randomized value applied to the odd part of $f$. Averaging over the original sampled instance therefore gives the three-query OXR acceptance probability for that odd part.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.SignQueryCheck.oddSymmetrizedValue_eq_oddPart`.
