<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Length Oracle

**Claim.** On the encoded pair $(h,\mathrm{bits}(i))$, the input-length oracle returns true exactly when $i<|h|$.

**Proof.** The claimed computation is precisely the length-oracle identity for the underlying oracle (\texttt{drop\_len}): on the encoded pair of $h$ and the binary representation of $i$, its answer is the decision of $i<|h|$. The oracle used here is that same length oracle, so the identity gives the result directly.

**Key facts.** `Complexity.drop_len`.
