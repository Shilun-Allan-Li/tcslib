<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPair_inverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Encoding and Decoding

**Claim.** If decoding a finite Boolean word $x$ returns the pair $(a,v)$, then $x$ is the encoding of $(a,v)$.

**Proof.** Proceed by induction on the word, considering its first two bits together. The empty word and every one-bit word cannot decode successfully, so the implication holds vacuously. For a word with at least two bits, inspect those first bits. If they are both false, decoding recursively decodes the tail and prepends false to the first decoded component. A successful recursive decode, together with the induction hypothesis, identifies the tail as the encoding of the decoded pair; putting the two initial false bits back gives exactly the encoding with false prepended to that component. The case of two initial true bits is identical, with true prepended instead. If the initial bits are false then true, they are the separator: decoding returns the empty first component and the remaining tail as the second, which is precisely the encoding of that pair. If the initial bits are true then false, decoding fails, so the implication is vacuous. These cases establish the claim.
