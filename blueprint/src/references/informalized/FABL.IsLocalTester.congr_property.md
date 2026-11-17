<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.IsLocalTester.congr_property -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under Equivalent Properties

**Claim.** If two properties contain exactly the same functions, then a tester that is local for the first property at a given rate is local for the second at that same rate.

**Proof.** The rate condition is unchanged. If $f$ belongs to the second property, equivalence puts it in the first, so perfect acceptance follows from the original tester guarantee. For soundness, take a function far from every member of the second property. Every member of the first also belongs to the second, again by equivalence. The function is therefore far from every member of the first, and the original soundness guarantee gives the required rejection probability.
