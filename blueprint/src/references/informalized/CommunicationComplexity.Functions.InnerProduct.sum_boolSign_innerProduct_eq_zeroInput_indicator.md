<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.sum_boolSign_innerProduct_eq_zeroInput_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner-product character sum

**Claim.** For a fixed input $z$, the sum of the Boolean signs of its mod-$2$ inner products with all inputs $x$ is $2^n$ when $z$ is zero and $0$ otherwise.

**Proof.** If $z$ is the zero input, every inner product with $z$ is false (\texttt{innerProduct\_zero\_right}), so every Boolean sign is $+1$. There are $2^n$ inputs, yielding the first case. If $z$ is not zero, it has a coordinate $i$ with $z_i=\mathrm{true}$ (\texttt{exists\_true\_of\_ne\_zeroInput}). Flipping the $i$th bit of $x$ is a bijection on the inputs (\texttt{flipAt\_bijective}) and reverses the sign of the inner product character, by the vanishing result for a nonzero index (\texttt{sum\_boolSign\_innerProduct\_eq\_zero\_of\_exists\_true}). Thus the sum is zero.

**Key facts.** `CommunicationComplexity.Functions.InnerProduct.innerProduct_zero_right`, `CommunicationComplexity.exists_true_of_ne_zeroInput`, `CommunicationComplexity.Functions.InnerProduct.sum_boolSign_innerProduct_eq_zero_of_exists_true`.
