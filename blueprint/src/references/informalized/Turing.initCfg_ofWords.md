<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Convention.lean :: Turing.initCfg_ofWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Blank Work Tapes

**Claim.** For a Boolean input word, the machine’s initial configuration is the configuration in its initial state with empty work words on every tape.

**Proof.** Unfolding the definitions, both configurations have state $q_0$, input-head position $1$, work-head positions all $0$, and empty output. The work-tape functions also agree: the left side has no symbol at any cell by the definition of the initial configuration, while on the right the buffer for each empty word is blank at every integer position (`Turing.FinTM.bufferTape_nil`). Thus all configuration components coincide.

**Key facts.** `Turing.FinTM.bufferTape_nil`.
