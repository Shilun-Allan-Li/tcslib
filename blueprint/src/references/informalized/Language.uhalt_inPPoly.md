<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHalt.lean :: Language.uhalt_inPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal halting has polynomial circuit size

**Claim.** The universal halting language belongs to polynomial size: it has a family of well-formed Boolean acyclic circuits with fan-in at most two and size bounded by \(a(n+1)^k\) for some natural numbers \(a,k\).

**Proof.** First, the universal halting language has polynomial-size layered circuits by `Language.uhalt_inLayeredPPoly`. The conversion theorem for layered polynomial-size circuits states that every language in this class also has polynomial-size Boolean acyclic circuits with fan-in at most two (`Language.InLayeredPPoly.inPPoly`). Applying it gives the claimed circuit family and bound.

**Key facts.** `Language.uhalt_inLayeredPPoly`, `Language.InLayeredPPoly.inPPoly`.
