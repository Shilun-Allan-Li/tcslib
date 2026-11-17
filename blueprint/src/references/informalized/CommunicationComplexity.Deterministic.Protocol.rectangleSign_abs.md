<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean :: CommunicationComplexity.Deterministic.Protocol.rectangleSign_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rectangle sign has absolute value one

**Claim.** For any protocol with Boolean outputs and any set of input pairs, the rectangle sign is either $+1$ or $-1$, and thus has absolute value $1$.

**Proof.** By definition, the rectangle sign is $1$ if every point of the set has output false, and is $-1$ otherwise. In either case its absolute value is $1$.
