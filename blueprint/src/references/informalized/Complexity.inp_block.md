<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.inp_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Input-Cell Update

**Claim.** Under the hypotheses on source values and earlier configuration blocks, applying the input-cell update to the evaluated padded source list yields exactly the input-cell encoding at time $t$ and position $p$ for the input determined by the source values on $(x,[])$.

**Proof.** Set $w$ to be the input whose bits are the source values on $(x,[])$, and let $l$ be the evaluated padded source list. Its first eleven entries are precisely the eleven local inputs to the input-cell update; padding does not alter these entries. The proof also identifies the input symbol at position $p$: its presence bit records whether $1\le p\le |\ell|$, and its value bit is the corresponding source value, using the hypothesis that every source in $\ell$ has the same value on $(x,B)$ as on $(x,[])$. If $p$ is outside this range, the input symbol is absent.

Proceed by cases on time. At time zero, the input head starts at position $1$, so the base input-cell update rule (`cfgF_inp_zero`) applies. The local flags, input-symbol bits, and same-time chain bits agree with the required values: the first two follow from the initial-time and position flags, the input bits from the identification above, and the chain bits from the definition of the input chain. This yields the desired input-cell encoding.

At a successor time $t+1$, the three previous-time head indicators at positions $p-1,p,p+1$ are read from the corresponding earlier input-cell blocks. Each such block precedes the current block: the input-index-before-next-block bound (`inpIdx_lt_succ`) and the block-index formulas give this strict inequality. The earlier-block hypothesis therefore identifies those blocks with the correct configuration encodings (`eval_block`), and the input-cell layout theorem (`cfgExp_inpIdx`) identifies their relevant bits with the previous input-cell encodings. The same reasoning identifies the two same-time chain inputs from the cell at $p-1$ when $p>0$; at $p=0$ they are empty by definition.

The previous snapshot portion of the source list evaluates to the encoding of the snapshot at time $t$ (`prevSnapSrcs_eval`): its block index is below the current input-cell index, and the earlier-block hypothesis applies. Decoding this encoding recovers the snapshot (`snapDecode_snapEncode`). Thus the local inputs satisfy the hypotheses of the successor input-cell update rule (`cfgF_inp_succ`): they encode the previous snapshot, the boundary and input-symbol data, the three neighboring head indicators, and the chain carried from position $p-1$. That rule gives the desired input-cell encoding at time $t+1$. The two time cases establish the result.

**Key facts.** `Complexity.cfgExp_inpIdx`, `Complexity.inpIdx_lt_succ`, `Complexity.eval_block`, `Complexity.prevSnapSrcs_eval`, `Complexity.snapDecode_snapEncode`, `Complexity.cfgF_inp_zero`, `Complexity.cfgF_inp_succ`.
