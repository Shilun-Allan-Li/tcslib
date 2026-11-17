<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.add_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition of Encoded Naturals

**Claim.** Decoding the self-delimiting pair encoding of the binary representations of $a$ and $b$, then adding their decoded values and taking the binary representation, produces the binary representation of $a+b$.

**Proof.** For this encoded input, pair decoding recovers the two original bit lists: the repeated-bit portions are restored and the delimiter separates them. Thus the two decoded components are $\mathrm{Nat.bits}(a)$ and $\mathrm{Nat.bits}(b)$. Their bit values are $a$ and $b$, respectively, by the fact that evaluating the binary representation recovers the natural number ($\texttt{bitsVal\_bits}$). The addition procedure therefore takes the binary representation of $a+b$, as claimed.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.
