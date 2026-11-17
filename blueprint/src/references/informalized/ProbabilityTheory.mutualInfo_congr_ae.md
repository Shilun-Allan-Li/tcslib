<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.mutualInfo_congr_ae -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost-sure invariance of mutual information

**Claim.** If two pairs of measurable random variables agree coordinatewise almost everywhere, then their mutual informations are equal.

**Proof.** The almost-everywhere equalities for the two coordinates combine to show that the pair-valued random variables $(X,Y)$ and $(X',Y')$ agree almost everywhere. Their distributions are therefore identical: they are identically distributed. Mutual information depends only on the joint and marginal distributions, so identically distributed pairs have equal mutual information (`ProbabilityTheory.IdentDistrib.mutualInfo_eq`).
