<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTerm_eq_average_fixedAliceInfoTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average of Fixed-Coordinate Information

**Claim.** Alice’s information term equals the average over coordinates of the fixed-coordinate information terms.

**Proof.** First express Alice’s information term as a sum over the fibers of the special coordinate, weighted by the probability $1/n$ of each coordinate (`aliceInfoTerm_eq_sum_specialCoordinate_fiber_info`). On the fiber where the special coordinate is $i$, the dynamic conditioning information equals the fixed-coordinate term for $i$ (`aliceDynamicConditioning_fiber_info_eq_fixedAliceInfoTerm`). Substitution gives $\sum_i (1/n)\,\mathrm{fixedAliceInfoTerm}(i)$. Factoring the constant $1/n$ out of the finite sum yields the stated average.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTerm_eq_sum_specialCoordinate_fiber_info`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceDynamicConditioning_fiber_info_eq_fixedAliceInfoTerm`.
