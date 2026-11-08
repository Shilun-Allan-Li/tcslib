<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.dpInit_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Dynamic-Programming Encoding

**Claim.** The initial dynamic-programming encoding is the pair of the context encoding and the word encoding, for each code $a$ below $V=B(|x|+1)^e$, of the base value that is $1$ exactly when the corresponding configuration belongs to the accepting-configuration language, with $s=c(|\operatorname{bits}(|x|)|+1)$.

**Proof.** Unfold the initial encoding and replace the code word by its encoded list of binary codes (`Randomized.BPLInP.codesW_eq`). The map-on-encoded-lists identity (`Complexity.BinArith.mapW_pairEncode`) and the decoder for an encoded list (`Complexity.BinArith.decWords_encWords`) turn the construction into one entry for each $a<V$. For each such $a$, decoding the paired context recovers the input, space bound, and code (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`). The initial-language membership criterion (`Complexity.Codec.mem_initLang`) then says that the indicator is true exactly when the initial configuration code equals $a$. This is precisely the time-zero dynamic-programming value: its base case is $1$ for that code and $0$ otherwise. Re-encoding these entries gives the claimed pair.

**Key facts.** `Randomized.BPLInP.codesW_eq`, `Complexity.BinArith.mapW_pairEncode`, `Complexity.BinArith.decWords_encWords`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.Codec.mem_initLang`.
