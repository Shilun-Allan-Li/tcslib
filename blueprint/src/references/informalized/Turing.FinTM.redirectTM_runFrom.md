<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.redirectTM_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration under redirection

**Claim.** After $t$ steps, the redirected machine has the state determined by the original state and the last bit of the original output: it carries the original state and that bit if the original machine is running, and if the original machine has halted it is halted exactly when the last bit is $b$, otherwise entering the loop state. The input-head position, work tapes, and work-tape-head positions agree with the original configuration, and the redirected output is empty.

**Proof.** Use the run correspondence lemma to replace the redirected run after $t$ steps by the redirected image of the original machine's configuration at time $t$ (`redirect_run`). The definition of that image leaves the input-head position, work tapes, and work-tape-head positions unchanged, and sets the output to the empty word. Its state is obtained by applying the redirection rule to the original state and the last bit of its output: a live original state becomes a live paired state; a halted original state becomes halted when the stored last bit is $b$, and otherwise becomes the loop state. These component identities give all the asserted equalities.

**Key facts.** `Turing.FinTM.redirect_run`.
