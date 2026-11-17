<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clTrack_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One complete tracking round

**Claim.** The tracking machine completes a round within $2W+4$ steps, remains in the bank phase at every intermediate positive time, and ends at the canonical configuration for the source machine's successor with the selected counters incremented and a valid boundary tag.

**Proof.** 1. Compute the displacement vector $d$ determined by the source transition. The one-step simulation property (`Complexity.clTrack_source`) supplies a valid tag for the successor and shows that the tracking machine's first step enters the bank phase, initializing each counter's control state according to whether its index is selected by $d$.

2. The bank completes its counting procedure after some $t\le 2W+2$ steps, without having reached its all-zero exit state earlier, and leaves each selected counter incremented and each unselected counter unchanged (`Complexity.clBank_first`). The bank's simultaneous run is the collection of the individual counter runs (`Complexity.clBank_run`). Hence the tracking machine stays in the bank phase for the intermediate steps and, after the bank finishes, reaches the exit configuration. The bounds give $0<t+2\le 2W+4$.

3. During the bank run, the tracking machine carries the bank computation alongside the successor source configuration and its tapes; this is the step-by-step lifting property (`Complexity.clLeft_until`). The configuration fields have the required arrangement by the bank/reference equality (`Complexity.clTrack_frame`). At the exit, dispatch returns to the canonical tracking configuration, as specified by `Complexity.clTrack_dispatch`. Taking $\tau=t+2$ therefore gives the asserted endpoint, with counter values updated by exactly the selection rule.

**Key facts.** `Complexity.clTrack_source`, `Complexity.clBank_first`, `Complexity.clBank_run`, `Complexity.clLeft_until`, `Complexity.clTrack_frame`, `Complexity.clTrack_dispatch`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
