<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.Traj.branch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Branching Trajectory Properties

**Claim.** If each of the three contracts satisfies its respective trajectory property, then the branching contract satisfies the first-phase property during the first phase and the property for the selected branch afterward.

**Proof.** Fix a run of the branching contract and a time within its duration. The branching trajectory description (Turing.Contract.branch_traj) separates the run into two portions. Up to and including the first contract's duration, the composed run agrees with the first machine's run, so the first trajectory hypothesis gives the first-phase property and hence the required disjunction. After that duration, write the time as the first duration plus one transition and a remaining time $v$. The first contract's endpoint is in the set consisting of the two designated exit states. If its state is $e_1$, the trajectory description identifies the remaining run with the first branch's run from its renamed endpoint; the branch precondition hypothesis and that branch's trajectory property give the desired branch property. If its state is not $e_1$, membership in the two-element exit set forces it to be $e_2$. The same trajectory description identifies the remaining run with the second branch's run, and its precondition and trajectory property give the other branch property. In either case the indicated disjunction holds.

**Key facts.** `Turing.Contract.branch_traj`, `Turing.Contract.mapState_state`.
