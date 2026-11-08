<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arReadCfg_dispatch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Read-to-Write Dispatch

**Claim.** At the final counter of the read sweep, one simulator step produces the write-sweep configuration for the action prescribed by the original machine on the symbols scanned in the original configuration, with write counter $N$.

**Proof.** At counter $N+1$, the read buffer contains the full block code of each scanned work-tape symbol, by the full-buffer property (`Turing.FinTM.arBuffer_full`). Decoding each such code recovers the original optional symbol (`Turing.FinTM.arDecode_code`). Thus the simulator takes the dispatch branch and consults the original transition function with the same work-tape symbols as the configuration. The encoded input symbol also agrees with the original input symbol after applying the binary embedding (`Turing.FinTM.arCfg_input`), so this is precisely the action specified in the claim. The transition enters the write sweep at counter $N$, with the action’s pending state, writes, and head movements. At this full-write boundary, the tail tape agrees everywhere with the encoding of the original tape after the action (`Turing.FinTM.arTail_full`). Comparing the configuration fields now gives the claimed write-sweep configuration: the input head follows the action, the work-tape heads are at offset $N$, and the output is extended by the encoded action output.

**Key facts.** `Turing.FinTM.arBuffer_full`, `Turing.FinTM.arDecode_code`, `Turing.FinTM.arCfg_input`, `Turing.FinTM.arTail_full`.
