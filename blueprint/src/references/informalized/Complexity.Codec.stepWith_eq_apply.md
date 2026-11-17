<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Step.lean :: Complexity.Codec.stepWith_eq_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice Step as an Applied Action

**Claim.** A one-step transition with choice $b$ is the configuration obtained by applying the effective action to $C$: the machine’s chosen transition when the state is present, and the idle action when it is halted.

**Proof.** Split according to whether the configuration’s state is absent or is some state $q$. In the halted case, `stepWith_of_halt` says that the machine remains at $C$. The effective action is then the idle action. Applying it leaves the state, work tapes, head positions, and output unchanged; its input-head movement is zero, so `moveInputPos_zero` shows that the input position is unchanged as well. Extensionality of configurations therefore identifies the result with $C$. In the nonhalted case, unfolding the definitions shows directly that both sides apply the transition action prescribed for state $q$, choice $b$, the current input symbol, and the work-tape head symbols.

**Key facts.** `Turing.NDTM.stepWith_of_halt`, `Turing.moveInputPos_zero`.
