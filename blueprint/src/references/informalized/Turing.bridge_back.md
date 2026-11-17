<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_back -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward loading of the input

**Claim.** For every program $c$, Boolean string $x$, and $j\le |x|$, the bridging machine can move from the configuration positioned at $j$, in its backward-reading state with the stack word of the suffix of $x$ beginning at $j$ on its main stack, to the configuration at the left boundary with the full stack word of $x$, the translated initial execution state, and empty output.

**Proof.** Induct on $j$. At $j=0$, the head is already at the left boundary and the main stack already contains the word of $x$. One transition in the backward-reading state, with no input symbol under the head, enters the translated execution state and leaves the stacks, head position, and output unchanged.

For the step from $j$ to $j+1$, first consider the configuration at position $j+1$. Its input symbol is the $j$th bit of $x$. The machine takes two transitions: it enters a temporary state carrying that bit, then pushes the corresponding bit symbol onto the main stack and moves the input head one place left. The pushed symbol followed by the stack word of the suffix beginning at $j+1$ is exactly the stack word of the suffix beginning at $j$. Thus the resulting configuration is the induction hypothesis's starting configuration at position $j$. The induction hypothesis supplies a finite run from there to the desired boundary configuration. Concatenating the two-step run with that run proves the claim. The run-concatenation fact used here is that two finite runs with matching endpoint and starting point compose to a finite run (\texttt{bridgeReach_trans}).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.bridgeCfg_idle`, `Turing.bridgeReach_trans`, `Turing.inputSymbolInner`, `Turing.bridgeCfg_push_input`, `Turing.bridgeStore_push`, `Turing.moveInputPos_neg_of_ne_left`.
