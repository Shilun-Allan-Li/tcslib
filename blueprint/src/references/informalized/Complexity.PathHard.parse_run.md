<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun.lean :: Complexity.PathHard.parse_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing and Run Behavior

**Claim.** For the specified register program started on a bit string $y$ of length at most $B$, a failed pair parse leads to a false answer while every pre-halting configuration obeys the guard. Whenever $y$ is the pairing of $x$ and $\beta$, the run reaches the copy instruction for $x$ with the stated register values, and all earlier configurations obey the guard.

**Proof.** First, the input-length loop queries the second oracle component to count the length of $y$. The input-length oracle returns true exactly for positions below $|y|$, so this loop reaches the scan state with the length register set to $|y|$ and all other registers unchanged. The bound $|y|\le B$ ensures that the register bound is preserved throughout this loop; its precondition and register-bound invariant are supplied by the input-length-loop result (Complexity.LogProg.inputLength_loop).

Next the aligned pair scan examines the input in matching pairs of bits, using the first oracle component to read each bit. It advances the scan pointer across the doubled encoding and separator while maintaining the guard. If the parser fails, this scan reaches the false-answer state; the halt result for that state then gives a false halt with the guard holding at every earlier configuration (Complexity.PathHard.ans_halt). Composing the length-counting and scan runs uses transitivity of guarded reachability, and composing with the halt certificate yields the claimed halting behavior (Complexity.LogProg.AReach.trans; Complexity.LogProg.AReach.halt).

If $y=\operatorname{pairEncode}(x,\beta)$, the pairing decoder returns $(x,\beta)$ (Turing.pairDecode_pairEncode), so the scan instead reaches the copy instruction. Its pointer is $2|x|+2$, its length register remains $|y|$, and all other registers remain zero; these are exactly the registers specified by the aligned-scan result. The same reachability composition gives the full run from the initial state, and reflexivity supplies the final reachability step to the stated endpoint (Complexity.LogProg.AReach.trans; Complexity.LogProg.AReach.refl).

**Key facts.** `Complexity.LogProg.inputLength_loop`, `Complexity.PathHard.orc_len`, `Complexity.LogProg.alignedPair_loop`, `Complexity.PathHard.orc_bit`, `Complexity.LogProg.AReach.trans`, `Complexity.PathHard.ans_halt`, `Complexity.LogProg.AReach.halt`, `Turing.pairDecode_pairEncode`, `Complexity.LogProg.AReach.refl`.
