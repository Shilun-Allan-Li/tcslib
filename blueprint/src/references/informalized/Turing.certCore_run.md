<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.certCore_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Certificate Run

**Claim.** The certificate machine halts within four steps of the original machine’s halting time, and outputs the one-bit verdict that the original output is exactly $[\mathrm{true}]$.

**Proof.** Choose the first halting time $r$ of the original run. The first-halt principle (\texttt{Turing.MultiTapeTM.exists\_first\_halt}) gives $r\le D$, guarantees the run is nonhalting before $r$, and identifies the configuration at $r$ with the one at time $D$. The virtual-host simulation theorem (\texttt{Turing.vhostEmitTM\_runFrom}) then carries the original run through time $r$, preserving its output and ensuring that the simulated machine is live before $r$ and halted at $r$. Apply the silent-return embedding theorem (\texttt{Turing.embedSilentRetTM\_run}): since the capacity tape is outside the embedded slots, the simulation is transferred to the larger tape bank, and its halt is routed to the return state. At that point, the capacity tape contains the captured output, with its head at the end of that word; this is precisely the content and head-position guarantee of the capture lemma (\texttt{Turing.cert\_capture\_fields}). The three-step verdict procedure (\texttt{Turing.certVerdict\_run}) reads that captured word and halts after appending the bit that tests whether it is $[\mathrm{true}]$. Finally, the seam-composition run theorem (\texttt{Turing.seamCompTM\_run\_ofCfg}) combines the silent simulation and verdict phases: the return state is reached after $r+1$ steps, and the verdict phase takes three more. Thus the total time is $r+1+3\le D+4$, with the asserted halted state and output.

**Key facts.** `Turing.MultiTapeTM.exists_first_halt`, `Turing.vhostEmitTM_runFrom`, `Turing.embedSilentRetTM_run`, `Turing.cert_capture_fields`, `Turing.certVerdict_run`, `Turing.seamCompTM_run_ofCfg`.
