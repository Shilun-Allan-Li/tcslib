<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPayload_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for the Extracted Payload

**Claim.** For every Boolean word $x$, the second component returned by the aligned pair parser, or the empty word if parsing is undefined, has length at most the length of $x$.

**Proof.** Split into the cases where parsing $x$ is undefined or returns a pair. In the undefined case the payload is empty, so the bound is immediate. In the defined case, write the returned pair as $(a,b)$. The parser's reconstruction property says that $x$ is the pair encoding of $a$ and $b$ (Turing.eq_pairEncode_of_pairDecode). The encoding consists of symbols encoding the first component and a delimiter followed by the second component, so its length is at least the length of $b$. Hence the extracted payload has length at most $|x|$.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`.
