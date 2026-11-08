<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Mul.lean :: Complexity.BinArith.length_le_of_mulInv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for multiplication witnesses

**Claim.** If $S$ is a multiplication witness for $z$ satisfying the stated conditions, then $|S|\le 4(|z|+1)$.

**Proof.** Unpack the witness, leaving $S$ as the nested pair encoding of $A,B,C$. First bound the length of $C$. Its value is the product of the values of the two projections of $z$, minus the nonnegative contribution from $C$'s equation; hence $\operatorname{val}(C)\le \operatorname{val}(\operatorname{fst}(z))\operatorname{val}(\operatorname{snd}(z))$. Each bit string's value is strictly below the power of two determined by its length (`Complexity.LogProg.bitsVal_lt_two_pow`), so the product is strictly below $2^{|\operatorname{fst}(z)|+|\operatorname{snd}(z)|}$. Because $C$ is the canonical binary representation of its value, the canonical representation length bound (`Complexity.LogProg.length_bits_le`) gives $|C|\le |\operatorname{fst}(z)|+|\operatorname{snd}(z)|$. Now apply the pair encoding length formula (`Turing.length_pairEncode`) to the two nested encodings. The witness bound on $|A|+|B|$ and the component bound $2|\operatorname{fst}(z)|+|\operatorname{snd}(z)|\le |z|$ (`Complexity.length_pair_components_le`) reduce the resulting estimate to $|S|\le 4(|z|+1)$.

**Key facts.** `Complexity.LogProg.bitsVal_lt_two_pow`, `Complexity.LogProg.length_bits_le`, `Complexity.length_pair_components_le`, `Turing.length_pairEncode`.
