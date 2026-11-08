<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.bplTest_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-Space Test and Path Count

**Claim.** Under the stated size bound, the Boolean test is true exactly when twice the bounded accepting-path count exceeds the power of two specified in the statement.

**Proof.** Write $s=c(|\operatorname{bits}(|x|)|+1)$ and $V=B(|x|+1)^e$. First identify the word computed by the dynamic-programming procedure: after $V$ iterations its accumulated-count word is the binary expansion of the dynamic-programming value at time and code bound $V$, starting from the initial configuration code. The iteration formula (`Randomized.BPLInP.iterate_dpInit`) and the context identity (`Randomized.BPLInP.ctxW_eq`) put the computation in terms of the parameters $s,V$. Decoding the encoded list of candidate codes (`Complexity.BinArith.decWords_encWords`) and the zip-with encoding identity (`Complexity.BinArith.zipWithW_pairEncode`) reduce the final selection to the entries indexed by codes below $V$. The initial-language characterization (`Complexity.Codec.mem_initLang`) makes the selector retain exactly the initial configuration's code; the code bound (`Complexity.Codec.cfgCode_lt`) and the hypothesis ensure that code is among those indices. The encoded sum therefore equals the required dynamic-programming value, using the list-to-finite-sum identity (`Randomized.BPLInP.sumW_encWords`, `Randomized.BPLInP.sum_map_range`) and the binary-list mapping identity (`Randomized.BPLInP.map_bits`). Finally, the padded-power value formula (`Randomized.BPLInP.bitsVal_pow2W`) converts the left input to the comparison into $2^V$. Evaluating the binary value of the other input yields twice the path count, so the Boolean comparison is precisely the asserted strict inequality.

**Key facts.** `Randomized.BPLInP.iterate_dpInit`, `Randomized.BPLInP.ctxW_eq`, `Complexity.BinArith.decWords_encWords`, `Complexity.BinArith.zipWithW_pairEncode`, `Complexity.Codec.mem_initLang`, `Complexity.Codec.cfgCode_lt`, `Randomized.BPLInP.sumW_encWords`, `Randomized.BPLInP.sum_map_range`, `Randomized.BPLInP.map_bits`, `Randomized.BPLInP.bitsVal_pow2W`.
