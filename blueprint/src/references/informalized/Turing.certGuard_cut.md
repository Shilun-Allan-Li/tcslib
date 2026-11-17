<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.certGuard_cut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Immediate Accepting State

**Claim.** At every time $t<1$, the certificate-guard machine’s state is not true.

**Proof.** Since $t$ is a natural number and $t<1$, necessarily $t=0$. At time zero the run is still at its starting configuration, whose state is false. Hence its state cannot be true.
