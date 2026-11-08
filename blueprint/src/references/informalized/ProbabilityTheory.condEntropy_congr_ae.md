<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Conditioning.lean :: ProbabilityTheory.condEntropy_congr_ae -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional entropy under almost-sure equality

**Claim.** If two pairs of finite-range measurable random variables agree almost everywhere on a probability space, their conditional entropies are equal.

**Proof.** The almost-sure equalities of the two coordinates imply that the pairs $(X,Y)$ and $(X',Y')$ are almost surely equal. Almost-surely equal measurable random variables have the same distribution, so these pairs are identically distributed. The conditional-entropy invariance theorem under equality of pair laws then gives $H[X\mid Y;\mu]=H[X'\mid Y';\mu]$.
