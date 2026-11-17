<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.beq_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality Test on Encoded Naturals

**Claim.** On the self-delimiting encoding of the binary representations of $a$ and $b$, the Boolean equality test returns the decision of whether $a=b$.

**Proof.** Pair decoding of the self-delimiting encoding recovers $\mathrm{Nat.bits}(a)$ and $\mathrm{Nat.bits}(b)$. Evaluating these bit lists gives $a$ and $b$, respectively, since the value of a natural number's binary representation is the original number ($\texttt{bitsVal\_bits}$). The test compares those values for equality, so its result is exactly the decision of $a=b$.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.
