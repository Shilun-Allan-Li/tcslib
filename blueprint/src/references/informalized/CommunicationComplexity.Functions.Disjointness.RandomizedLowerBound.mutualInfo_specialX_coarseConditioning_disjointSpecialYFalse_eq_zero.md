<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of the Special Bit

**Claim.** Under the hard distribution conditioned on disjointness and on Bob’s special bit being false, Alice’s special bit has zero mutual information with the coarse variable.

**Proof.** Write $\mu$ for this conditional probability measure. The proof first applies the finite-valued independence criterion: it is enough to show, for every bit $b$ and coarse value $c$, that the measure of the joint fiber is the product of the measures of the two individual fibers. The conditional law is a probability measure (\texttt{disjointSpecialYFalseMeasure_isProbabilityMeasure}), so the criterion applies. The joint-fiber formula gives its measure as $\tfrac12$ times the measure of the coarse fiber (\texttt{disjointSpecialYFalseMeasure_measureReal_specialX_inter_coarseConditioning}); the special-bit marginal formula says that the fiber for any $b$ has measure $\tfrac12$ (\texttt{disjointSpecialYFalseMeasure_measureReal_specialX_singleton}). These two identities make the joint fiber measure exactly the product of the marginals. Thus the two variables are independent, and the equivalence between independence and zero mutual information yields the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_isProbabilityMeasure`, `ProbabilityTheory.indepFun_of_measureReal_inter_preimage_singleton_eq_mul`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_measureReal_specialX_inter_coarseConditioning`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_measureReal_specialX_singleton`.
