<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.orcN_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Length Oracle on Encoded Indices

**Claim.** For every Boolean string $x$ and every $k\le |x|$, the first oracle queried on the pair encoding of $x$ and the binary representation of $k$ returns true exactly when $k<|x|$.

**Proof.** The first oracle is the indicator function of the input-length language, whose defining predicate asks whether the encoded index is less than the input length. The encoding lemma `indicator_indexLang_pairEncode` evaluates this indicator on the pair encoding of $x$ and the binary representation of $k$ as the decision of that predicate. Substituting the input-length predicate gives exactly the decision of $k<|x|$.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`.
