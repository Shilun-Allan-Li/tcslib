<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Conditioning.lean :: ProbabilityTheory.IdentDistrib.cond_of_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional law of a component

**Claim.** If two pairs $(X,Y)$ and $(X',Y')$ have the same law, then conditioning each space on the event that its second coordinate belongs to a measurable set $s$ gives the same law for the first coordinates.

**Proof.** To compare the conditioned laws, evaluate them on an arbitrary measurable set $t$ in the range of the first coordinate. The conditioned-measure formula gives the first conditioned probability as $\mu(Y^{-1}(s))^{-1}\mu(Y^{-1}(s)\cap X^{-1}(t))$, and gives the corresponding formula for the primed variables. Equality of the pair laws, applied to the second-coordinate projection, makes the two conditioning-event masses equal. Applied to the rectangle $t\times s$, it makes the two intersection masses equal. Hence the conditioned probabilities agree for every such $t$, which is equality of the laws of $X$ and $X'$ under the conditioned measures.
