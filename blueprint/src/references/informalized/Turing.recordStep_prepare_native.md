<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_prepare_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation of the Native Input Scan

**Claim.** Under the stated width and input-length hypotheses, the record machine can identify whether its input head is at the right boundary, set the counter target to the boundary position or the current position accordingly, and reach the seek stage with the counter word decremented exactly $q+1$ times within the stated time and head-displacement bounds.

**Proof.** Write $e$ for the embedding of Boolean digits into record symbols, and let the fuel word be the all-true word of length $|w|$. First, the machine scans tape 3 and replaces its scanned cells by true digits. The map-snapshot result ( `recordStep_map_snapshot` ) supplies the endpoint, nonverdict control history, and head bounds for this pass; the phase-transition result ( `recordStep_phase_run` ) then advances control to the boundary probe.

The probe-run result ( `recordStep_probe_run` ) determines whether the current input-head position is the right boundary. If it is, the probe returns the head to position $|x|$; otherwise it leaves the position unchanged. Thus its returned position $p$ is at most $|x|$. The phase-transition result packages this probe run and enters the counter-saving stage with the boundary flag stored in the record data.

The all-true fuel word represents $2^{|w|}-1$; this follows from the complement-value identity ( `recordStep_complement_value` ). The reserve hypothesis ensures that the probe's returned position is strictly below this value. The save-transport result ( `recordStep_save_transport` ) therefore runs the counter loop until it has performed $p+1$ decrements, reaching the escape control with the counter word representing those decrements. Taking $q=p$ gives the required value: by the probe's boundary behavior, $q=|x|$ when the flag is true and otherwise $q$ is the original head position. A further phase transition enters the seek stage at state $s_0$. Composing the fuel scan, probe, and save runs with `recordRun_trans` gives the stated endpoint. Their bounds, together with $p\le |x|$, yield the claimed time limit; their head-displacement bounds give radius $|w|+1$, and the phase-run histories ensure that neither verdict state occurs before the final time.

**Key facts.** `Turing.recordStep_complement_value`, `Turing.recordStep_map_snapshot`, `Turing.recordStep_phase_run`, `Turing.recordStep_probe_run`, `Turing.recordStep_save_transport`, `Turing.recordRun_trans`.
