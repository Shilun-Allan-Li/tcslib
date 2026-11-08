<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_timed_control_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Control Configuration

**Claim.** For each Boolean input word, the timed conditional machine's initial configuration is the control configuration associated with the initial configuration of $D$.

**Proof.** Compare the five components of the configurations. Their states, input-head positions, and outputs agree directly from the definitions: the initial state is embedded into the control state, the input head starts at position $1$, and both outputs are empty. For each work-tape index, split according to whether it lies in the block reserved for $D$ and the two branches or is the final extra tape. On an index in the first block, the initial configuration has a blank tape and head at $0$, matching the lifted configuration. On the extra tape, the captured empty output buffer is blank and its head is at the length of the empty word, also $0$. Thus every component agrees.
