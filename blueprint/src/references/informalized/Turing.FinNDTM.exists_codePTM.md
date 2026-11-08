<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPHard.lean :: Turing.FinNDTM.exists_codePTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coding a binary-choice machine

**Claim.** Every finite-state nondeterministic Turing machine over the binary alphabet has a binary-choice machine with finitely many work tapes and a state set that is a finite initial segment of the natural numbers, whose runs on every input and choice word halt exactly when the original runs halt and produce the same output.

**Proof.** Let $Q$ be the state set of the given machine. It is nonempty because it contains the initial state, so its cardinality is positive and can be written as $(|Q|-1)+1$. Choose an equivalence between $Q$ and the finite initial segment of that size, and relabel the machine's states along this equivalence to obtain the coded machine. The state-relabeling run theorem (`relabelState_runWith`) says that, for every input, choice word, and starting configuration, the relabeled run is the state-relabeling of the original run. Applied to the initial configuration, this preserves the output exactly. It also preserves whether the state is absent: relabeling maps a present state to a present state and leaves absence unchanged. Hence the runs halt under exactly the same condition and have identical outputs.

**Key facts.** `Turing.NDTM.relabelState_runWith`.
