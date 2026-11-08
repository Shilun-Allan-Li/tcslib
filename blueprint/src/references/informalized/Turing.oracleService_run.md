<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleService_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle service simulation

**Claim.** Under the stated blank-bank, head-position, source-window, and first-exit hypotheses, the composed machine reaches the specified result configuration after $2|arg|+3+t$ steps, and does not reach the designated second-component exit state earlier.

**Proof.** First designate the embedded bank tape that will hold the copied argument. The oracle call view (`oracleCall_view`) identifies the embedded-call configuration with a host configuration in which that tape contains the buffer for $arg$. The copy routine places that buffer on the initially blank bank tape in $2|arg|+2$ steps and does not reach its done state earlier (`oracleCopy_intoBlank`). The relocated-call result (`oracleRelocatedCall`) then simulates the given run of $C$ for $t$ steps, producing the buffer for $result$ in that bank tape; its first-exit hypothesis ensures that the simulated call does not reach the designated exit state at an earlier call time. The view lemma also identifies the endpoint with the stated host configuration. Finally, the seam composition runs the copy phase, takes one transition across the seam, and runs the call phase, so its total time is $(2|arg|+2)+1+t=2|arg|+3+t$ (`seamCompTM_run_ofCfg`). The corresponding first-return result (`seamCompTM_firstReturn_ofCfg`), using the copy routine's earlier-time bound and the call's first-exit bound, excludes the designated second-component state at every earlier time.

**Key facts.** `Turing.oracleCall_view`, `Turing.oracleCopy_intoBlank`, `Turing.oracleRelocatedCall`, `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`.
