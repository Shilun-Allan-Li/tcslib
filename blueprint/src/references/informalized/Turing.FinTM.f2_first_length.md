<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_first_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Decoded First Component

**Claim.** The first component returned by pair decoding, using the empty word when decoding is undefined, has length at most the length of the input word.

**Proof.** Split according to whether decoding is undefined. If it is undefined, the chosen default is empty, so the bound is immediate. If decoding returns $(a,b)$, the inverse property of decoding says the input is the pair encoding of $a$ and $b$ (the inverse property of pair decoding, `Turing.FinTM.f2_catalogPair_inverse`). The encoding has length $2|a|+2+|b|$ (`Turing.length_pairEncode`), which is at least $|a|$.

**Key facts.** `Turing.FinTM.f2_catalogPair_inverse`, `Turing.length_pairEncode`.
