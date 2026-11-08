<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.xorInput_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinatewise xor evaluation

**Claim.** At each coordinate, the coordinatewise xor of two Boolean inputs is the xor of their bits at that coordinate.

**Proof.** By definition, the coordinatewise xor sends $i$ to $y_i\oplus z_i$. Thus evaluating it at $i$ gives exactly the claimed equality.
