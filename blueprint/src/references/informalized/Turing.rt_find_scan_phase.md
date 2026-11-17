<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_find_scan_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Host Behavior During a Scan Phase

**Claim.** While the machine scans field $j$, the host agrees with the standalone scanning machine through time $2|w|+2$, with its state tagged by phase $j$. One more step redirects the host from the completed scan to the specified combined phase-and-control state $q$.

**Proof.** The scan theorem `rt_find_scan` supplies the standalone machine's configuration after $2|w|+2$ steps and shows that no completed scan state occurs earlier. Therefore the host redirect is disabled at every earlier step: forward and backward scan states do not redirect, and the completed state is excluded by the scan theorem's earlier-time clause. The phase-host theorem (`phaseHostTM_run`) then identifies the host run with the standalone run, tagged by phase $j$, through the completion time. At completion, the assumed redirect equation sends the completed accumulator state to $q$, so the theorem also gives the host configuration after the additional redirect step. The endpoint state-tagging equality follows by comparing configuration fields.

**Key facts.** `Turing.rt_find_scan`, `Turing.phaseHostTM_run`.
