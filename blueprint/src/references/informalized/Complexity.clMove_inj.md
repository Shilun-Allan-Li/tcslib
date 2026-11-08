<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMove_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Move Displacements

**Claim.** If two move symbols have the same integer displacement, then the symbols are equal.

**Proof.** Each move symbol is one of the three possibilities with displacement $-1$, $0$, or $1$. Split into the possible values of the two symbols. Their integer displacements agree only when both are the same one of these three values, so the symbols themselves are equal.
