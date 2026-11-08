<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Conditioning.lean :: ProbabilityTheory.IdentDistrib.condMutualInfo_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional mutual information from joint law

**Claim.** For finite-range measurable random variables on probability spaces, conditional mutual information is determined by the joint law of the triple: identically distributed triples have equal conditional mutual information.

**Proof.** The conditional mutual information identity expresses each side as the conditional entropy of the pair given the third variable, minus the conditional entropies of each component given that variable. Equality of the triple laws implies equality of the corresponding laws of $(X,Z)$, $(Y,Z)$, and $((X,Y),Z)$: apply the appropriate coordinate projection to the triple. Conditional entropy is determined by these joint laws, so each of the three terms agrees across the two probability spaces. Subtracting gives the stated equality.
