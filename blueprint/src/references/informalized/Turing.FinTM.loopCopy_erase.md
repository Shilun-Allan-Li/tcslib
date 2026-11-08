<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopCopy_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing a Copied Cell

**Claim.** Changing the copying tape to blank at the frontier cell of the remaining suffix gives the copying tape whose processed prefix includes that cell’s bit.

**Proof.** Compare the tapes at each integer cell. At the frontier, the update makes the cell blank, which is exactly what the longer processed-prefix definition prescribes. At every other cell, the update changes nothing. The cutoff conditions for the old and new processed prefixes agree away from the frontier, since the new prefix has length one more than the old one; the underlying stored word is unchanged, as reassociation identifies the two concatenations. Thus the tapes agree everywhere.
