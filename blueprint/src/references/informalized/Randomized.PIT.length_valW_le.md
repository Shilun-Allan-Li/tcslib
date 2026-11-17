<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.length_valW_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for the reduced value

**Claim.** For every bit string $D$, the word representing the value reduced modulo the key extracted from $D$ has length at most the length of the raw input extracted from $D$.

**Proof.** The encoding and decoding identities for paired words (`Complexity.pairFstD_pairEncode` and `Complexity.pairSndD_pairEncode`) reduce the decoded first component of the encoded pair to `rawValW D`, and the second component to `sK D`. The key has value $\mathrm{bitsVal}(sRaw D)+1$: adding the encoded one contributes one, using the bit-value identity for natural-number bit representations (`Complexity.LogProg.bitsVal_bits`). Hence the remainder of `\mathrm{bitsVal}(rawValW D)$ modulo this key is strictly smaller than the key, and therefore at most $\mathrm{bitsVal}(sRaw D)$. Apply the bit-length bound (`Complexity.BinArith.length_bits_le_of_le`) with the word $sRaw D$ to conclude that the bit representation of this remainder has length at most $|sRaw D|$.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.length_bits_le_of_le`.
