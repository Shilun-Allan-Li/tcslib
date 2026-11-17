<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.indicator_eq_of_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Boolean Indicators

**Claim.** If membership of $y$ in a language $L$ is equivalent to a decidable proposition $P$, then the Boolean indicator of $L$ at $y$ equals the Boolean truth value of $P$.

**Proof.** The indicator of a set at a point is the Boolean decision of whether that point belongs to the set (`indicator_eq_decide`). Thus the left side is the decision of $y\in L$. The given equivalence identifies this proposition with $P$, and equivalent propositions have the same Boolean decision. Therefore the indicator equals $\operatorname{decide}(P)$.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`.
