<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mutualInfo_specialX_zVariable_eq_aliceCoarseInfoTermSpecialYFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mutual Information Decomposition

**Claim.** For a deterministic protocol, under the hard distribution conditioned on disjointness and on Bob’s special-coordinate bit being false, the mutual information between Alice’s special bit and the statistic consisting of the transcript, special coordinate, Alice’s preceding bits, and Bob’s following bits equals the conditional mutual information between Alice’s special bit and the transcript given the latter three components.

**Proof.** Let $Q$ denote the coarse variable and $M$ the transcript, and let $Z$ be the statistic containing both. First, $Z$ is just an injective recoding of $(Q,M)$: its fields recover the special coordinate, Alice’s bits before it, Bob’s bits after it, and the transcript. The injective-recoding invariance of mutual information (\texttt{ProbabilityTheory.mutualInfo_comp_right_of_injective}) therefore identifies the information Alice’s special bit has with $Z$ and with $(Q,M)$. The product-variable chain rule then gives $I(X_T;(Q,M))=I(X_T;Q)+I(X_T;M\mid Q)$ (\texttt{ProbabilityTheory.mutualInfo_prod_right_eq_add}). The first term vanishes by the established independence of Alice’s special bit and the coarse variable under this conditional law (\texttt{mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero}). What remains is precisely the conditional mutual information in the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_isProbabilityMeasure`, `ProbabilityTheory.mutualInfo_comp_right_of_injective`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.ZType.ext`, `ProbabilityTheory.mutualInfo_prod_right_eq_add`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero`.
