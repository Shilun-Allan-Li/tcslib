<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.RoundContract.counterLoopDone_traj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter-loop head trajectories

**Claim.** During every time covered by the counter-loop contract, the original work-head positions agree with those of the machine at some time within one of the rounds indexed below the counter value, or at the start of the final orbit configuration.

**Proof.** Fix the parameter, starting configuration, and a time within the contract duration. Regard the body configuration extracted from the counter-loop configuration as the starting point of the machine’s round orbit. The precondition supplies the round preconditions and return-to-anchor conditions needed at all indices below the counter value. The orbit anchor theorem (`Turing.RoundContract.orbit_anchor`) therefore identifies the state at each such orbit index as the anchor. The orbit round theorem (`Turing.RoundContract.orbit_round`) then supplies a valid round, with its prescribed duration, at each index below the counter value; the endpoint equality follows by identifying the next orbit point with the endpoint of that round using the successor formula for round orbits (`Turing.roundOrbit_succ`) and the contract’s run equation. Apply the counter-loop done witness theorem (`Turing.counterLoopTMVia_done_witness`) with these round facts and the encoded counter-tape contents. Its segment invariant says that at every time up to the prescribed duration, the first $k$ head positions match a run of $M$ from some orbit configuration: either the orbit index is below the counter value and the within-round time is at most that round’s duration, or the index is the counter value and the within-round time is zero. Finally, `Turing.counterLoopCfg_body` identifies the first $k$ tapes of the counter-loop configuration with the extracted body configuration, so the witness gives exactly the asserted head-position equality.

**Key facts.** `Turing.RoundContract.orbit_anchor`, `Turing.RoundContract.orbit_round`, `Turing.roundOrbit_succ`, `Turing.counterLoopTMVia_done_witness`, `Turing.counterLoopCfg_body`.
