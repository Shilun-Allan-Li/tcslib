<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_moveWord_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying and Clearing a Tape Word

**Claim.** The composed machine copies the source word to the destination and clears the source in the stated time, without reaching its final phase earlier and while keeping every head within the stated distance of its initial position.

**Proof.** Map the initial state to the copy machine’s sweep state. The copy-run theorem (`Turing.copyTM_run_ofCfg`) applies to the source buffer and distinct tapes: after $2|w|+2$ steps, the destination contains the copy, and the machine reaches its copy exit for the first time. Its head-position bounds place both active heads within the interval from one cell left of their origins to $|w|$ cells right. Since the source and destination are distinct, the copied destination word does not disturb the source, so the source still satisfies the same buffer hypothesis for clearing. Apply the clear-run theorem (`Turing.clearTM_run_ofCfg`) to clear the source in another $2|w|+2$ steps, again with its first-exit and head-position conclusions. The seam-composition theorem (`Turing.rt_copy_seam`) joins these two runs: it accounts for the extra transition between phases, preserves the first-arrival conclusion, and combines their shared head-radius bound. Thus the total duration is $2|w|+2+1+2|w|+2=4|w|+5$. Rewriting the endpoint configuration gives a blank source segment, a copied destination segment, and unchanged remaining data.

**Key facts.** `Turing.copyTM_run_ofCfg`, `Turing.clearTM_run_ofCfg`, `Turing.rt_copy_seam`.
