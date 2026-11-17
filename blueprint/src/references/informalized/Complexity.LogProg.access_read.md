<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading an Input Bit

**Claim.** Subject to the stated head-position bound, the read-phase configuration reaches a safe configuration recording the optional input bit at the index selected by the label, with the other parameters and tape-$2$ head unchanged.

**Proof.** The read simulation scans the selected index on the input while keeping the other configuration data fixed. Its finite-run invariant bounds both the scanning head and the input position, and records the read result as the optional symbol at that index (`Complexity.LogProg.readIn_run`). The selected tape is either tape $0$ or tape $3$, so it is distinct from tape $1$ and tape $2$; consequently the simulation's temporary head and tape updates do not interfere with tape $2$ or with the other counters. The initial configuration is safe by the assumed bounds (`Complexity.LogProg.accessCfg_safe`), and the run invariant shows every intermediate configuration is safe. Turning this safe finite run into an access path (`Complexity.LogProg.accessPath_of_run`) gives the claimed path and endpoint.

**Key facts.** `Complexity.LogProg.readIn_run`, `Complexity.LogProg.accessCfg_safe`, `Complexity.LogProg.accessPath_of_run`.
