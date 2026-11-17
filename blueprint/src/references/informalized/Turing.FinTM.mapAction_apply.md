<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.mapAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Threaded-Map Action

**Claim.** Applying the specified administrative action to a threaded-map configuration updates its controller state, input-head position, capture-head position, and output exactly as described, leaving the underlying tape bank unchanged.

**Proof.** Compare the two configurations component by component. The action sets the state to $q'$, moves the input head from $p$ according to $m$, and appends the optional symbol $b$ to the output word. For each work tape, if its index belongs to the original machine's tape bank, the action makes no write and gives it zero movement, so its contents and head position remain those encoded by $c$. The additional capture tape is also not written, and its head moves by $d$, changing its displacement from $h$ to $h+d$. Thus all components agree with the stated threaded-map configuration.
