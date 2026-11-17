<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_scan_preserves -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation by a Two-Pass Scan

**Claim.** If the scan starts in forward phase with state $a$, its scanned tape contains $w$, and the forward-and-backward transducer returns $(b,w)$, then after $2|w|+2$ steps the configuration is unchanged except for its state, which is the completed phase carrying $b$. No completed phase occurs earlier; the scanned head stays in the stated interval and all other work heads remain fixed.

**Proof.** Apply the scan-run theorem (`scanTM_run_ofCfg`) to the tape contents and initial forward state. It gives the configuration after the forward pass, the return pass, and the two boundary steps, as well as the earlier-state exclusion and head-position bounds. The scan theorem writes the returned word only on the scanned interval. The hypothesis that the full scan result is $(b,w)$ makes the returned state and word exactly $b$ and $w$. On the interval the original tape already equals the buffer of $w$, by the content hypothesis; outside it both the original and returned buffers are blank. Thus the tape is unchanged everywhere. The other configuration fields are unchanged by the scan-run description, yielding the asserted configuration identity.

**Key facts.** `Turing.scanTM_run_ofCfg`.
