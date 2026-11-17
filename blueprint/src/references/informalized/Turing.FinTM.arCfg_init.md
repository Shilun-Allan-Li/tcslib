<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arCfg_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding the initial configuration

**Claim.** Under the assumption that the blank symbol is coded as the all-blank block, the binary simulator's initial configuration equals the encoding of the original machine's initial configuration on the embedded input.

**Proof.** Compare the configuration components. The initial states agree because the simulator starts in the ready state corresponding to the original initial state. Their input head positions agree, since the embedded input has the same length as the binary input. For each tape and integer position, the original initial tape is blank, so its encoded block is $E(\mathrm{none})$, which is all blank by hypothesis; thus the simulated tape contents agree. The encoded head positions agree because both initial heads are at zero, and the simulator's output is empty just as the original output is empty (bitwise decoding preserves the empty list). These componentwise equalities establish equality of the configurations.
