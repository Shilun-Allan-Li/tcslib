<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopFuelCaptured_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Fuel Frame

**Claim.** A halted fuel-machine configuration, after capture and relocation, is the controller frame with phase zero, inherited input-head position, blank flag and counter tapes, the output buffered on the payload track, the flag head at zero, the counter head at the output length, and empty output.

**Proof.** Unpack the captured relocated configuration and compare its fields with those of the stated frame. Its state is the return control state because the fuel configuration is halted; its input position and output are the inherited input position and the empty output. For work tapes and head positions, split the indices into the fuel-machine block, the inserted single tape, and the final payload tape. In the fuel block the relocation supplies blank tapes with heads at zero; the inserted tape is likewise blank with head zero. At the final index, capture supplies the buffer of the fuel output and places its head at the output length. These fieldwise equalities establish equality of the configurations.
