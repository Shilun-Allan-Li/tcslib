<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.RoundContract.counterLoopEscape_traj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter-loop escape trajectories

**Claim.** At every time up to the counter-loop contract duration, the original work-head positions agree with those of the machine at a time within one of the rounds through the specified escape round, or at the start of the next orbit configuration.

**Proof.** Fix the parameter, initial configuration, and a time within the contract duration. Extract the body configuration and write $r_0$ for the specified round index. The hypotheses give round preconditions through $r_0$, and return to the anchor for every earlier endpoint. The orbit anchor theorem (`Turing.RoundContract.orbit_anchor`) identifies the relevant orbit configurations as starting in the anchor state. In particular, the endpoint of round $r_0$ is the next orbit configuration: the successor formula for round orbits (`Turing.roundOrbit_succ`) identifies it with the run for that round’s contract duration, and the contract run equation identifies that run with its prescribed endpoint. Thus the endpoint has state $ex$ by hypothesis. The orbit round theorem (`Turing.RoundContract.orbit_round`) supplies the round conditions for each index at most $r_0$. Apply the counter-loop escape witness theorem (`Turing.counterLoopTMVia_escape_witness`) using these rounds, the counter-tape encoding, and the identified escape endpoint. Its segment invariant gives, at the chosen time, an orbit index $r$ and within-round time $u$: either $r\le r_0$ with $u$ at most that round’s duration, or $r=r_0+1$ and $u=0$, and the original head positions agree with the corresponding run of $M$. The configuration identity `Turing.counterLoopCfg_body` aligns the first $k$ heads of the counter-loop configuration with those of the extracted body run, yielding the claimed equality.

**Key facts.** `Turing.RoundContract.orbit_anchor`, `Turing.roundOrbit_succ`, `Turing.RoundContract.orbit_round`, `Turing.counterLoopTMVia_escape_witness`, `Turing.counterLoopCfg_body`.
