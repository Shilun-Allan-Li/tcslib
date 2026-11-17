<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCapture_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Captured Step

**Claim.** When the original configuration has a present state, one step of the capture machine from its embedded configuration equals the embedding of the original machine's one-step result.

**Proof.** The original configuration's state is present, so write it as $\operatorname{some}(q)$. The embedded configuration then has state $\operatorname{some}(\operatorname{inl}(\operatorname{some}(q)))$, which selects the capture machine's branch that simulates the original transition. Its original-tape reads agree with those of the source configuration, and the input-head position is unchanged by embedding. Let $a$ be the original machine's transition action at $q$. The capture transition applies $a$ on the original tapes, stores any emitted symbol on the buffer tape, leaves the other added tapes untouched, and preserves the original transition's input movement and successor state. Compare the resulting configurations tape block by tape block. On the buffer tape, if $a$ emits a bit $b$, the output grows from $w$ to $w++[b]$ and the buffer update is precisely to write $b$ at position $|w|$ (`bufferTape_append`); if no bit is emitted, the buffer does not change. The heads, state, input position, remaining tapes, and empty external output then agree by their definitions. Hence the one-step configurations are equal.

**Key facts.** `Turing.FinTM.bufferTape_append`.
