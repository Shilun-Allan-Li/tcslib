<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBFEncoding.lean :: Complexity.QBF.quantOfBit_quantBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quantifier Bit Round Trip

**Claim.** Encoding either Boolean quantifier as a bit and interpreting that bit as a quantifier returns the original quantifier.

**Proof.** There are two cases. The existential quantifier is encoded as true, which is interpreted as existential; the universal quantifier is encoded as false, which is interpreted as universal. In each case the result is the original quantifier.
