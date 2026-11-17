<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.Action.apply_workTapes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-tape update under an action

**Claim.** Applying an action changes work tape $i$ only at the cell under its head, writing the prescribed symbol there when one is specified and otherwise retaining the symbol already scanned.

**Proof.** Split according to whether the action prescribes a symbol for tape $i$. If it prescribes none, applying the action leaves the entire tape unchanged. The displayed update also leaves every other cell unchanged, and at the head position writes the old scanned symbol, since the default value of the optional write is that scanned symbol. If the action prescribes a symbol, applying it updates the tape at the head position with that symbol; the displayed expression does the same because the prescribed symbol is the value returned by the option’s defaulting operation. Thus the two descriptions agree in both cases.
