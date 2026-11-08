<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.gStep_encState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Evaluator Step

**Claim.** One encoded evaluator step on the encoding of the context, word, and values agrees with the encoding of one abstract evaluator step, using modulus $\mathrm{bitsVal}(R)+1$ and input values $i\mapsto\mathrm{bitsVal}(P_i)+1$.

**Proof.** Decode the fields of the encoded state. The pairing projections recover the context, current word, index counter, and list of prior values (`pairFstD_pairEncode`, `pairSndD_pairEncode`). The arithmetic circuit that computes the next value reads the input or prior gate values by indexed lookup; the lookup facts identify these with the corresponding list entries (`getW_pairEncode`, `getW_pairEncode_bits`). Converting the resulting bit strings back to natural numbers uses $\mathrm{bitsVal}(\mathrm{Nat.bits}(m))=m$ (`bitsVal_bits`). Consequently the encoded value computed by the gate-value circuit is precisely the bit representation of the abstract value for this word. Now compare the two step rules. If the word is already done, both preserve the state. If it is accepted by the validity check, both replace it by the same remainder, advance the counter, and append the computed value; the encoding of the extended value list is the old encoding followed by the encoding of that value (`encWords_append_singleton`). If it is invalid, both clear the word and preserve the values. These cases establish equality of the resulting encoded states.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.getW_pairEncode`, `Complexity.BinArith.getW_pairEncode_bits`, `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.encWords_append_singleton`.
