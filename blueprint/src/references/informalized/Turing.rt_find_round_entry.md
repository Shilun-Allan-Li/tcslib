<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_find_round_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return to the Round Boundary

**Claim.** From the read control on tape 0 encoding nonempty fields, the first positive time the machine reaches either the read or exit control exists, is at most $7(|J|+1)$, and has neither control at any intervening positive time. At that time the head displacement and control are determined by whether the fold of the joined tape $J$ is accepted.

**Proof.** Forget the combined phase-and-control state of $c$ and regard its control as the unset Boolean in the read phase. The configuration map preserves all tape data, so the tape-encoding hypothesis applies to this read-component configuration. The entry theorem (`rt_find_entry`) supplies a positive time with the stated bound, no intervening visit to either distinguished control, and the specified endpoint. Reattaching the phase tag turns its endpoint equality into the corresponding equality for the original combined configuration. In particular, the supplied time is a positive time at which the state is read or exit. The clock is defined as the least positive such time whenever one exists. Since no earlier positive time reaches either control, the clock equals the supplied time, by `rt_findClock_eq`. Substituting this equality yields all the claimed properties for the clock-selected time.

**Key facts.** `Turing.rt_find_entry`, `Turing.rt_findClock_eq`.
