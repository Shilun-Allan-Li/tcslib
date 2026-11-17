<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.divInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Division invariant under one step

**Claim.** A division step preserves the division invariant; when the pending bit string is nonempty its length decreases strictly, and when it is empty the state is unchanged.

**Proof.** Unpack the invariant, so the state consists of the fixed divisor together with a processed prefix $R$, remainder $r$, and quotient $q$. If $R$ is empty, the step's stopping branch returns the same state, and the invariant and the two length conclusions follow directly. Otherwise write $R=c::R'$. The bit $c$ is either zero or one, and the step removes it from the pending prefix. The reversed-prefix value splits as the value for $R'$ plus $c2^{|R'|}$, while the new remainder candidate has value $c+2\operatorname{val}(r)$. The branch test compares this candidate with the divisor. If it is at least the divisor, the algorithm subtracts the divisor, records a one in the quotient, and the updated quotient-remainder equation and strict remainder bound follow from the one-bit division calculation (`div_value_step`). If it is smaller, the candidate is retained and a zero is recorded; the other case of that same calculation gives the equation and remainder bound. The length constraints persist: the new pending prefix is shorter by one, and the new remainder or its binary representation is bounded using `length_bits_le_of_le`; the quotient length bound follows from adding one quotient bit. The value of the new quotient bits is computed by `bitsVal_bits`.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.bitsVal_append_singleton`, `Complexity.BinArith.div_value_step`, `Complexity.BinArith.length_bits_le_of_le`, `Complexity.LogProg.bitsVal_bits`.
