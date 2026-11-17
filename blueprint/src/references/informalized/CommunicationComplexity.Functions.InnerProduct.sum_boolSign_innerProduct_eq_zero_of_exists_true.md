<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.sum_boolSign_innerProduct_eq_zero_of_exists_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing character sum

**Claim.** If $z$ has a true coordinate, the sum over all inputs $x$ of the Boolean sign of their mod-$2$ inner product with $z$ is zero.

**Proof.** Let $S$ denote the sum. The map that flips coordinate $i$ is a bijection, so reindexing the sum by this map leaves its value unchanged (\texttt{flipAt\_bijective}). Since $z_i$ is true, flipping that coordinate toggles the inner product (\texttt{innerProduct\_flipAt\_eq\_xor}); the Boolean sign therefore changes to its negative, using the multiplicative sign rule for XOR (\texttt{boolSign\_xor}). Consequently the reindexed sum is $-S$, while bijectivity says it is $S$. Thus $S=-S$, which over the reals implies $S=0$.

**Key facts.** `CommunicationComplexity.Functions.InnerProduct.innerProduct_flipAt_eq_xor`, `CommunicationComplexity.boolSign_xor`, `CommunicationComplexity.flipAt_bijective`.
