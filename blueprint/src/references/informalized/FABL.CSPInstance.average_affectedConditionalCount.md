<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.average_affectedConditionalCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average affected conditional count

**Claim.** Averaging over a label drawn from the variable’s law, the conditional expected satisfaction count of constraints containing that variable equals their original total expected satisfaction count.

**Proof.** Consider the affected constraints as a multiset and induct on its size. For the empty multiset, both sums are zero. For a nonempty multiset, separate one constraint from the rest. Its variable occurs in its scope, so averaging its conditional expected satisfaction indicator over the original law recovers its original expected indicator (the marginal replacement averaging identity, `FABL.CSPConstraint.average_localExpectedIndicator_replace`). The induction hypothesis gives the same equality for the remaining constraints, since each remains affected. Linearity of expectation combines these equalities with the contribution of the separated constraint, proving the result.

**Key facts.** `FABL.CSPConstraint.average_localExpectedIndicator_replace`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`.
