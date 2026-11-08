<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.Data.checkLang_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Check Language Is in Polynomial Time

**Claim.** If $d$’s language $R$ belongs to polynomial time, then the language that applies $d$’s check to the two decoded components of an input belongs to polynomial time.

**Proof.** Decode the input as a pair, then decode its first component again. The check uses these decoded pieces and several further nested pair components, along with the remaining suffixes. Each required component is obtained by repeated first- or second-component decoding; since both decoding functions are polynomial-time computable (`Complexity.polyTimeComputable_pairFstD` and `Complexity.polyTimeComputable_pairSndD`), all these composed decodings are polynomial-time computable (`Complexity.PolyTimeComputable.comp`). Pairing the computed components and appending the needed suffixes also preserves polynomial-time computability (`Complexity.PolyTimeComputable.pairEncode` and `Complexity.PolyTimeComputable.append`). The check itself is a conjunction of polynomially checkable conditions: the prescribed length bounds and equalities, membership of a decoded encoding in the circuit-value language, and membership of the final encoded string in $R$. Polynomial-time languages are closed under conjunction, disjunction, and complement (`Complexity.inter_mem_P`, `Complexity.union_mem_P`, and `Complexity.compl_mem_P`), and the preimage of a polynomial-time language under a polynomial-time computable map remains polynomial-time (`Complexity.preimage_mem_P`). The circuit-value language is polynomial-time (`BoolCircuit.CVAL_mem_P`), while $R$ is polynomial-time by assumption. Combining these closure facts gives the claimed polynomial-time check language.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.PolyTimeComputable.append`, `Complexity.Yap.lenLe_poly_mem_P`, `Complexity.Yap.lenEq_poly_mem_P`, `BoolCircuit.CVAL_mem_P`, `Complexity.preimage_mem_P`, `Complexity.inter_mem_P`, `Complexity.union_mem_P`, `Complexity.compl_mem_P`.
