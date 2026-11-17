<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHalt.lean :: Language.uhalt_inLayeredPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary halting language has polynomial layered size

**Claim.** The unary language whose permitted lengths form the universal halting set is recognized by finite layered circuits using the standard identity, NOT, and unbounded-fan-in AND gates, with size bounded by a polynomial in the input length.

**Proof.** The universal halting language is the unary language determined by the universal halting set: its strings are all-true Boolean lists whose lengths lie in that set. Apply the theorem that every unary language has polynomial-size layered circuits (`Language.unary_inLayeredPPoly`) to this set of lengths. This supplies the required circuit family, gate restriction, finiteness, and polynomial size bound.

**Key facts.** `Language.unary_inLayeredPPoly`.
