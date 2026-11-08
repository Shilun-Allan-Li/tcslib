<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_seek -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One step of the leftward seek

**Claim.** In the leftward-seek phase, the machine moves the guide head left and remains in that phase unless it reads the left-edge marker at $-R-1$; at that marker it moves right and enters the forward phase.

**Proof.** The guide symbol read in a macrostep configuration is the base guide-tape symbol at the current coordinate (`macroCfg_guide`). The left-edge characterization identifies the left-edge marker precisely at $g=-R-1$ (`guideTape_left`). Thus the transition enters the forward phase and moves right at that coordinate; at every other coordinate it remains in the leftward-seek phase and moves left. Applying these movements to the macrostep configuration updates the head coordinate as stated (`macroCfg_apply`).

**Key facts.** `Complexity.macroCfg_guide`, `Complexity.guideTape_left`, `Complexity.macroCfg_apply`.
