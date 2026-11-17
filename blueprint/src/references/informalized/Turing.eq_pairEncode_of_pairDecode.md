<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.eq_pairEncode_of_pairDecode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successful Parses Are Pair Encodings

**Claim.** If the aligned pair parser applied to $z$ returns $(a,b)$, then $z$ is the encoding formed by doubling each bit of $a$, appending $01$, and then appending $b$.

**Proof.** Use the parser's recursive cases on the initial symbols of $z$. If $z$ begins with $00$, successful parsing requires the parser to succeed on the remaining suffix, returning the tail of $a$ together with $b$. By induction that suffix is the encoding of those outputs; prepending $00$ gives the encoding of $a,b$. If $z$ begins with $11$, the same reasoning prepends $11$, again yielding the required encoding. If $z$ begins with $01$, the parser returns the empty first string and the remaining suffix as the second string, so the encoding is exactly the separator followed by that suffix. In every other initial pattern the parser returns failure, contradicting the assumed successful parse.
