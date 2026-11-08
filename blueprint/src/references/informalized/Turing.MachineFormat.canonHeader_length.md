<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonHeader_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for the Canonical Header

**Claim.** For every Boolean word $\alpha$, its canonical header has length at most $|\alpha|$.

**Proof.** If paired decoding fails, the canonical header is the empty word, so the bound is immediate. Otherwise write the decoded pair as $(bits,rest)$. A successful paired decode identifies $\alpha$ with the paired encoding of these words (`Turing.eq_pairEncode_of_pairDecode`). The length formula for that encoding (`Turing.length_pairEncode`) gives $|\alpha|=2|bits|+2+|rest|$, which is at least $|bits|$. In this case the canonical header is exactly $bits$, proving the bound.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`.
