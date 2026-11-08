<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.sum_boolSign_innerProduct_mul_eq_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh orthogonality

**Claim.** For any two Boolean inputs $y,z$, the sum over all $x$ of the product of their mod-$2$ inner-product signs is $2^n$ if $y=z$ and zero otherwise.

**Proof.** For each $x$, the product of the two signs equals the sign of the inner product of $x$ with the coordinatewise XOR of $y$ and $z$ (\texttt{boolSign\_innerProduct\_mul\_eq\_xorInput}). Summing over $x$ therefore gives the character sum for that XOR input. The character sum is $2^n$ if its index is zero and zero otherwise (\texttt{sum\_boolSign\_innerProduct\_eq\_zeroInput\_indicator}). Finally, the XOR of $y$ and $z$ is zero exactly when $y=z$ (\texttt{xorInput\_eq\_zeroInput\_iff}), giving the two cases.

**Key facts.** `CommunicationComplexity.Functions.InnerProduct.boolSign_innerProduct_mul_eq_xorInput`, `CommunicationComplexity.Functions.InnerProduct.sum_boolSign_innerProduct_eq_zeroInput_indicator`, `CommunicationComplexity.Functions.InnerProduct.xorInput_eq_zeroInput_iff`.
