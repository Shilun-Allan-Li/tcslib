<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_find_last_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accepting Final Scan

**Claim.** When the final field's scan produces an accepting state, the machine reaches the exit control after $2|w|+3$ steps, with all configuration data other than the control unchanged. Before that time it is neither in the read control with no stored bit nor in the exit control. Tape 0's head remains within one cell to the left of its initial position and $|w|$ cells to its right, while tape 1's head stays fixed.

**Proof.** The standalone two-way scan theorem says that scanning $w$ takes $2|w|+2$ steps, completes with the accumulator equal to the fold of $w$, and keeps the heads within the stated bounds (`rt_find_scan`). Since $j$ is the last field and the resulting accumulator is accepted, the host redirect from this completed scan goes to the exit control. The host-phase theorem (`rt_find_scan_phase`) shows that through the scan's completion the combined machine follows the standalone scan, tagged with phase $j$, and takes one additional step to the redirected exit configuration. This gives the endpoint after $2|w|+3$ steps and preserves the other configuration data. Before the scan completes, the standalone scan has not reached its completed state; the host therefore cannot yet redirect to either distinguished control. Its state remains nonhalting throughout, by persistence of a nonhalting state (`runFrom_state_ne_none_of_le`), so the tagged state exists at each earlier time and is neither distinguished control. The head bounds up to scan completion come from `rt_find_scan`; at the one final redirect step the heads do not move, so the same bounds hold at the endpoint.

**Key facts.** `Turing.rt_find_scan`, `Turing.rt_find_scan_phase`, `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`.
