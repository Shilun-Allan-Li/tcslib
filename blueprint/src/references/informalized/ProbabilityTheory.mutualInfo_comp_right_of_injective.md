<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.mutualInfo_comp_right_of_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance under injective recoding

**Claim.** Composing the second of two finite-range random variables with a measurable injection does not change their mutual information.

**Proof.** Write mutual information as the entropy of the first variable minus its conditional entropy given the second. Apply this identity both to $Y$ and to $f\circ Y$. Injectivity of $f$ ensures that observing $f(Y)$ determines $Y$, so the conditional entropy of the first variable given $f(Y)$ equals its conditional entropy given $Y$ (`condEntropy_of_injective'`). The entropy of the first variable is unchanged, and therefore the mutual informations are equal.
