<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonBitsTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Canonical-Bit Scan Machine

**Claim.** From the specified initial configuration, the canonical-bit scan machine reaches after exactly $2|w_i|+2$ steps the stated done configuration, and it does not reach any done state earlier.

**Proof.** Apply the scan-machine run theorem (`scanTM_run_ofCfg`) to the tape at index $i$, with the forward update that replaces the carried Boolean value by the symbol read and the backward update that leaves it unchanged. Its initial-state and tape-content hypotheses hold for the given configuration. The theorem gives the exact run time, excludes every done state at all earlier times, and identifies the final carried value and tape contents through the scan result. The scan-result formula for a fold (`scanResult_fold`) identifies that result as the left fold of the symbols, while `canonBits_fold` identifies this fold, starting from true, with the last-symbol test. The scan theorem’s final configuration updates only the scanned tape segment; here the scan restores that segment to its original contents, and all other configuration data are unchanged. Thus the final configuration is precisely the one claimed.

**Key facts.** `Turing.scanTM_run_ofCfg`, `Turing.scanResult_fold`, `Turing.MachineFormat.canonBits_fold`.
