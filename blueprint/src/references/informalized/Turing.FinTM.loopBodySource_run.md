<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopBodySource_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation by the Padded Source

**Claim.** For every configuration of the stop wrapper, every choice of contents and head positions for the additional tapes, and every time $t$, the extended source machine run for $t$ steps from the configuration adjoining those tapes agrees with adjoining the same tapes to the stop wrapper's configuration after $t$ steps.

**Proof.** Apply the general left-extension simulation theorem `leftCfg_run` to the stop wrapper and the extended source machine, with the identity state map. Its transition hypothesis says that, on an embedded state and the same input and work-tape readings, the extended machine performs exactly the wrapper's transition on the wrapper's tapes and leaves all added tapes unchanged. This is precisely how the extended source transition is defined: it uses the wrapper transition on the original tapes, while the added tapes receive no writes or head movement. The theorem therefore gives the stated equality for every number of steps, with the extra tapes and their head positions preserved.

**Key facts.** `Turing.FinTM.leftCfg_run`.
