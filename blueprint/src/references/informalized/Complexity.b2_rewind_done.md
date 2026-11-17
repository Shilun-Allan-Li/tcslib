<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_rewind_done -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatch into the Guessing Phase

**Claim.** One host step from the loader configuration in state $1$, with input head at position $0$, assembly buffer $x$, and assembly head at $|x|$, enters the guessing phase with the input-normalized scheduler initialized on $x$ and its guessed word empty.

**Proof.** At input position $0$, the host sees a blank symbol. In loader state $1$, this selects the transition that moves the input head right and enters the scheduler simulation at its initial state. This is a control action, which preserves all work tapes, work-tape heads, and the output while changing the state and input-head position (`Turing.FinTM.controlAction_apply`). The resulting input-head position is $1$, as in the initial scheduler configuration. The existing scheduler tapes are blank and its heads are at zero, while the added guess tape represents the empty word; these are precisely the initial scheduler data. Hence the resulting configuration is the asserted guessing-phase configuration.

**Key facts.** `Turing.FinTM.controlAction_apply`.
