<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_map_snapshot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mapped Scan Snapshot

**Claim.** Starting from the specified forward-scan snapshot, the scan that applies $f$ to the selected buffer reaches the stated done-state snapshot in $2|w|+2$ steps, avoids done states earlier, and satisfies the stated work-head bounds throughout.

**Proof.** In the initial snapshot, the selected tape stores $w$ relative to its head: this follows from the hypothesis identifying the corresponding buffer with $w$. The scan-run theorem `scanTM_run_ofCfg` therefore applies. Its endpoint is in the done phase, and its tape contents are given by the scan result. The identity `scanResult_map` says that this result preserves the scan state and replaces $w$ by its entrywise image under $f$. Thus the selected buffer is transformed as claimed.

It remains to identify the endpoint with the stated snapshot. On the selected tape, the scan theorem changes contents only across the scanned word's interval. Outside that interval, the original buffer agrees with the transformed buffer as well: positions outside the word yield no symbol in either buffer. The assumption that the selected buffer equals $w$ supplies the required identification on the interval. The other buffer and all nonselected tapes retain their snapshot contents. The same scan-run theorem gives avoidance of done states at every earlier time and bounds the selected head between one position left of its starting point and $|w|$ positions to its right; all other work heads remain fixed.

**Key facts.** `Turing.scanTM_run_ofCfg`, `Turing.scanResult_map`.
