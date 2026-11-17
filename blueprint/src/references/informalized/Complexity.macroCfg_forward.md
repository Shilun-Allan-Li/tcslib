<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_forward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One forward-scan step

**Claim.** In the forward phase, the machine moves the guide head right and stays in that phase unless it reads the right-edge marker at $R+1$; at that marker it moves left and enters the backward phase.

**Proof.** In a macrostep configuration, the guide symbol read is the base guide-tape content at the current guide coordinate (`macroCfg_guide`). The right-edge characterization says this symbol is the right-edge marker exactly when the coordinate is $R+1$ (`guideTape_right`). The forward transition therefore has two cases: at that coordinate it enters the backward phase and moves the guide head from $g$ to $g-1$; elsewhere it stays forward and moves to $g+1$. The updates to the phase and head coordinate follow from how applying a movement-only macro action changes a macrostep configuration (`macroCfg_apply`).

**Key facts.** `Complexity.macroCfg_guide`, `Complexity.guideTape_right`, `Complexity.macroCfg_apply`.
