<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_outer_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer Decoding or Rejection

**Claim.** For the specified initial registers and bound, the program either decodes a canonical tail of admissible width and reaches “scan” with register 5 equal to the tail's binary value, or rejects with answer false when the canonicality or width condition fails.

**Proof.** Write $h=\langle z,t\rangle$, let $a=2|z|+2$, and let $B=8(2C+3)(|h|+1)^{e+1}$. The initial vector fits within $B$; the encoding-length identity gives $|h|=a+|t|$ (`Turing.length_pairEncode`), and the available-bound estimate controls both the cap and all intermediate registers (`Complexity.comp_bound_room`).

At each position of the tail, the input-bit oracle reads the corresponding bit of $h$; the pair-encoding bit formula verifies this correspondence (`Complexity.comp_bit`, `Complexity.pairEncode_getD`). The canonical-tail loop consumes these bits while halving the cap register and checking that the tail's length fits its binary width. It reaches its completion state exactly when the tail is canonical and fits; otherwise it goes to the false-answer state (`Complexity.LogProg.canonicalTail_loop`). The equivalence between canonicality and a true final bit identifies the successful case (`Complexity.LogProg.drop_canon`).

In the successful case, clear the cap and pointer registers, copy the stop position into the pointer, and decode the tail into register 5. The bounded decoding loop accumulates the bits into their natural-number value; its accumulator estimate, together with the global bound-room estimate, keeps every register within $B$ (`Complexity.LogProg.boundedDecode_loop`, `Complexity.query_accumulator_bound`). The final transition reaches “scan” and stores $\operatorname{bitsVal}(t)$ in register 5. In the unsuccessful case, the tail-check loop already reaches the false-answer state; append the halting step that returns false (`Complexity.comp_ret`). The reachability lemmas combine these stages while retaining safety (`Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`, and `Complexity.LogProg.AReach.halt`).

**Key facts.** `Turing.length_pairEncode`, `Complexity.comp_bound_room`, `Complexity.comp_bit`, `Complexity.pairEncode_getD`, `Complexity.LogProg.canonicalTail_loop`, `Complexity.LogProg.drop_canon`, `Complexity.LogProg.boundedDecode_loop`, `Complexity.query_accumulator_bound`, `Complexity.comp_ret`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.halt`.
