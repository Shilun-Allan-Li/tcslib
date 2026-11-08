<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean :: Complexity.LogProg.apply_clAct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired-Tape Cleaning Action

**Claim.** Applying the cleaning action sets the state to $st'$, leaves the input-head position and output unchanged, updates only tape $i$ in each bank by its specified write instruction at the current head position, and advances each of those two head positions by $mv$.

**Proof.** Compare the configuration fields. The state is $st'$ by the action, and its input-head movement is zero, so the input position is unchanged (`Turing.moveInputPos_zero`). The output is unchanged because the action emits nothing. For tape contents, split the combined tape index into the first and second banks. In either bank, indices other than $i$ receive no write and therefore retain their contents. At index $i$, the resulting tape is unchanged if the write instruction is absent; if it specifies a symbol (including an empty-cell value), the tape is updated at that bank's current head position with that value. The same split shows that only head $i$ in each bank moves, and its new position is its old position plus $mv$.

**Key facts.** `Turing.moveInputPos_zero`.
