<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_nested_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested Drop Computation

**Claim.** For the encoded input $h=\langle z,\mathrm{bits}(q)\rangle$, the specified computation halts with the answer that is true exactly when $q$ is less than the length of the transformed word in length mode, or the $q$-th bit of that word is $1$ in bit mode. Every configuration before halting satisfies the computation invariant and the register bound.

**Proof.** Write $h=\langle z,\mathrm{bits}(q)\rangle$. The initial register values obey the stated bound, since the input contains the doubled encoding of $z$ and its separator; the length formula for pair encodings gives $2|z|+2\le |h|$. The register bound for the initial vector follows from the coordinate bounds in `dropValues_bound`. The preparation procedure carries the initial configuration to the layer-1 scan configuration while preserving the invariant (`drop_z_prepare`).

Apply the pair-scan result (`drop_pair_run`) to the first encoded component $z$, using stride $2$. The required bit alignment is supplied by the fact that reading position $2i$ of a pair encoding recovers its $i$-th first-component bit (`drop_first_read`). If decoding $z$ fails, the scan reaches a false-answer state with the pointer still within the register bound; the answer-state halting result then gives the required false output. The transformed word is empty in this case, so both requested predicates are false.

If decoding succeeds, write $z=\langle u,b'\rangle$, using the reconstruction theorem for successful decoding (`Turing.eq_pairEncode_of_pairDecode`). The scan now reaches the copy stage with the pointer positioned at the end of the outer encoding, and its register values agree with those required to process the nested pair. This follows from the scan's pointer-advance formula, the stride-2 encoding, and the pair-encoding length formula. The inner computation theorem (`drop_inner_run`) then handles the remaining nested decoding and indexed query, producing exactly the length-mode or bit-mode answer stated. Concatenating these reachability segments and the final halt establishes the invariant at every preceding configuration and the claimed answer.

**Key facts.** `Complexity.dropValues_bound`, `Complexity.drop_z_prepare`, `Complexity.drop_first_read`, `Complexity.drop_pair_run`, `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`, `Turing.pairDecode_pairEncode`, `Complexity.drop_inner_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.halt`, `Complexity.LogProg.register_update_le`, `Complexity.drop_ret`.
