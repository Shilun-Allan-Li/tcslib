<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.NDTM.flipOutput_stepWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipped output after one step

**Claim.** Stepping under a fixed choice with the machine that flips output, from a configuration with flipped output, gives the flipped version of the original machine's stepped configuration.

**Proof.** Split according to whether the starting configuration is halted. If it is halted, both machines leave their respective configurations unchanged, so the equality follows from the definition of flipping the output (Turing.NDTM.stepWith_of_halt). If it is active in state $q$, both transitions use the same state, input symbol, work-tape symbols and choice. Their actions therefore agree in every component except the output symbol. Applying either action updates the same state, head positions and work tapes. The output is the previous output followed by the optional emitted symbol; mapping Boolean negation over this appended list flips both the previous output and the emitted symbol. This is exactly the output produced by the flipped machine, giving the desired equality.

**Key facts.** `Turing.NDTM.stepWith_of_halt`.
