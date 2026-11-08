<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitBody_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial configuration of the round body

**Claim.** The round body's initial configuration on input $w$ is its anchor configuration with blank work tapes, all work-tape heads at $0$, input head at $1$, and empty output.

**Proof.** The general initial-configuration identity (`initCfg_ofWords`) says that a machine's initial configuration is the word configuration for its initial state with every work-tape word empty. The round body's initial state is the anchor state. Its empty work-tape words give blank tape contents, while the word-configuration construction places the input head at $1$, each work head at $0$, and the output at the empty word. The specified state-word assignment also gives the empty word on every tape when its candidate is empty.

**Key facts.** `Turing.initCfg_ofWords`.
