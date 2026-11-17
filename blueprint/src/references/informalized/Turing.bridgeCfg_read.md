<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Top Symbol on a Bridge Tape

**Claim.** The symbol under the work-tape head associated with stack name $k$ is the top element of $st(k)$ embedded in the bridge alphabet, or blank when that stack is empty.

**Proof.** The bridge configuration assigns work-tape index $i$ the tape contents determined by the stack named `bridgeKey(i)`, and places its head at the negative of that stack's length. For the index corresponding to $k$, the index-to-name mapping returns exactly $k$ (`Turing.bridgeKey_index`). At this head position, the bridge-stack reading rule says that the symbol read is the head of the list embedded in the bridge alphabet, with an empty list giving blank (`Turing.bridgeStack_read`). Combining these identifies the read symbol as the embedded top of $st(k)$, or blank if there is no top.

**Key facts.** `Turing.bridgeKey_index`, `Turing.bridgeStack_read`.
