<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: Language.unary_inPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary languages have polynomial circuit size

**Claim.** For every set \(S\subseteq\mathbb N\), the unary language determined by \(S\) is recognized by well-formed Boolean acyclic circuits with fan-in at most two and polynomial size.

**Proof.** The unary language has polynomial-size layered circuits by `Language.unary_inLayeredPPoly`. The general conversion from polynomial-size layered circuits to polynomial-size fan-in-two acyclic circuits (`Language.InLayeredPPoly.inPPoly`) then gives the asserted circuit family and bound.

**Key facts.** `Language.unary_inLayeredPPoly`, `Language.InLayeredPPoly.inPPoly`.
