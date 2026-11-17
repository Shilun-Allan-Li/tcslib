<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.e3LinDictatorTest_to_e3Sat_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine conversion to satisfiability testing

**Claim.** A dictator-versus-no-notables guarantee for the three-variable linearity testers transfers to their associated satisfiability testers, with acceptance parameters $3/4+\alpha/4$ and $3/4+\beta/4$ and error function $\lambda(\varepsilon)/4$.

**Proof.** The constructed satisfiability predicate family is finite (`FABL.maxE3SatSignPredicates_finite`), and every converted tester uses predicates from that family (`FABL.E3LinSignTester.toE3SatTester_usesMaxE3Sat`). The new parameters preserve positivity, their strict gap, and the upper bound of $1$ by elementary arithmetic from the corresponding hypotheses for $\alpha$ and $\beta$. The new error is $\lambda(\varepsilon)/4$: it remains in $[0,1]$ because the original error does, and it tends to zero because division by the constant $4$ preserves limits. Finally, the acceptance probability identity for the converted tester is $3/4$ plus one quarter of the original acceptance probability (`FABL.E3LinSignTester.acceptanceProbability_toE3SatTester`). Applying it to dictators converts the original completeness lower bound $\beta$ into $3/4+\beta/4$. Applying it to a function with small stable influences converts the original soundness upper bound $\alpha+\lambda(\varepsilon)$ into $3/4+\alpha/4+\lambda(\varepsilon)/4$. These are precisely the required completeness and soundness bounds.

**Key facts.** `FABL.maxE3SatSignPredicates_finite`, `FABL.E3LinSignTester.toE3SatTester_usesMaxE3Sat`, `FABL.E3LinSignTester.acceptanceProbability_toE3SatTester`.
