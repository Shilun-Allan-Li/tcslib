<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.mem_indexLang_compQ_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership under index-language composition

**Claim.** A string encodes a pair consisting of a binary string and a natural number's canonical bit expansion, satisfying the predicate after applying $f$ to the first component, exactly when its transformed string encodes a pair satisfying the predicate.

**Proof.** For the forward implication, write the given string as the encoding of $x$ and the canonical bit expansion of $i$, with the predicate holding of $f(x)$ and $i$. The transformation lemma (compQ_pairEncode) says that applying the transformation to this encoded pair produces exactly the encoding of $f(x)$ with the same bit expansion. That encoding therefore belongs to the target index language.

For the reverse implication, suppose the transformed string belongs to the target index language, so it is an encoding of some $y$ and the canonical bit expansion of some $i$. Unfold the transformation. A successful output must have parsed the original string as a pair $(x,b)$ and passed the test that $b$ is the canonical bit expansion of its represented number. The output is then the encoding of $(f(x),b)$. Injectivity of pair encoding (pairEncode_injective) identifies its components with $y$ and the canonical expansion of $i$, so $y=f(x)$ and $b=\operatorname{bits}(i)$. The decoding reconstruction fact (eq_pairEncode_of_pairDecode) now shows that the original string was the encoding of $(x,\operatorname{bits}(i))$, and its predicate is the one required on the left. If parsing fails or the canonicality test fails, the transformation outputs the empty string; this cannot be a target encoding because pair encodings are nonempty (pairEncode_ne_nil).

**Key facts.** `Complexity.compQ_pairEncode`, `Complexity.pairEncode_ne_nil`, `Turing.pairEncode_injective`, `Turing.eq_pairEncode_of_pairDecode`.
