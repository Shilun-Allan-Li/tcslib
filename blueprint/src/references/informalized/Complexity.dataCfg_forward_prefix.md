<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_forward_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Scan Invariant

**Claim.** For each $n\le 2R+1$, the simulator's forward scan advances its guide head by $n$ positions, preserves the decoded current payload at every coordinate, and fills the cached left-neighbor payload at each coordinate visited by the scan.

**Proof.** Proceed by induction on $n$. At $n=0$, choose the original tapes: the run has length zero, so the configuration is unchanged, the current-payload condition is the given hypothesis, and the interval of coordinates requiring a left-neighbor cache is empty. For the successor step, use the induction hypothesis to obtain tapes after $n$ steps, and write $g=-R+n$ for the current guide-head coordinate. The forward-step rule advances the head to $g+1$, sets the neighbor registers to the current payloads decoded at $g$, and updates each data tape at $g$ with a cell storing its current payload and the old neighbor-register payload. By the induction hypothesis, the decoded current payload at $g$ is $f(g)$; the old register is $f(g-1)$. Thus the update installs the required cell at $g$ and leaves the current payload unchanged there. At every other coordinate the tapes are unchanged, so their current payloads remain $f(z)$, and any previously established cache remains valid. The integer identities $g+1=-R+(n+1)$ and $g+1-1=g$ give the claimed head position and register value for the next stage.

**Key facts.** `Complexity.dataCfg_forward_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
