<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.xorInput_eq_zeroInput_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# When xor is zero

**Claim.** The coordinatewise xor of two $n$-bit Boolean inputs is the zero input exactly when the inputs are equal.

**Proof.** If their xor is zero, then at every coordinate its value is false. Fix a coordinate and consider the two possible Boolean values of each input bit. Of the four possibilities, xor is false only when the bits agree. Hence the inputs agree at every coordinate and are equal as functions. Conversely, if the inputs are equal, each coordinate xor is false, so their coordinatewise xor is the zero input.
