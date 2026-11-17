<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.obliviousSchedule_borrow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow-phase transition

**Claim.** When the budget tape contains the tagged bit $b$ and the schedule is in borrow phase with carry $c$, its transition writes $b\oplus c$, moves that tape head one cell right, leaves the other heads and the input head stationary, emits no output, and updates the carry to $c\wedge\lnot b$.

**Proof.** In the borrow phase, the schedule reads the budget-tape symbol. Under the hypothesis that this is the tagged bit $b$, its transition rule selects the branch that writes the bit $b\oplus c$ on the budget tape and moves that head right. The rule leaves the input head and other tapes stationary, emits no output, and changes the phase to borrow with carry $c\wedge\lnot b$. The auxiliary identity `oblAction_budget` identifies this action with the stated single-lane action.

**Key facts.** `Complexity.oblAction_budget`.
