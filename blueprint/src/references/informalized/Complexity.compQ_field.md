<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.compQ_field -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query on an encoded pair

**Claim.** Applying the query transformation to the encoding of $(x,b)$ returns the encoding of $(f(x),b)$ when $b$ is canonical, and returns the empty string otherwise.

**Proof.** The query transformation first decodes the pair encoding, which recovers exactly $(x,b)$ by `pairDecode_pairEncode`. It then checks whether the binary expansion of the value of $b$ is $b$ itself. This condition is equivalent to $b$ being canonical: every binary expansion is canonical (`canon_bits`), while a canonical string is recovered as the binary expansion of its value (`canon_eq_bits`). Therefore the check succeeds exactly when $\operatorname{Canon}(b)$ holds. In that case the transformation returns the encoding of $(f(x),b)$; when the check fails, its definition returns the empty string.

**Key facts.** `Turing.pairDecode_pairEncode`, `Complexity.LogProg.canon_bits`, `Complexity.LogProg.canon_eq_bits`.
