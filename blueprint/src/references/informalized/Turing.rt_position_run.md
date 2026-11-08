<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_position_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing a Marked Word

**Claim.** The composed machine writes `one` followed by $|w|-1$ copies of `zero` on the destination tape, reaches its final phase for the first time after $4|w|+10$ steps, and obeys the stated head bound.

**Proof.** Begin by viewing the configuration in the copy machine’s sweep phase. The copy-run theorem (`Turing.copyTM_run_ofCfg`) places a copy of $w$ on the destination in $2|w|+2$ steps. Distinctness of the tapes ensures that the copied word leaves the source available for later reference. The scan phase then applies the transformation that replaces every destination symbol by `zero` while preserving the scan’s state; the scan-run theorem (`Turing.scanTM_run_ofCfg`), together with the scan-result identity (`Turing.scanResult_map`), shows that the destination now contains $|w|$ zeros and the scan has returned to its exit. The writer puts `one` in the first cell in four steps (`Turing.writeConstTM_run_ofCfg`). Since $w$ is nonempty, this overwrites exactly the first zero and leaves the remaining $|w|-1$ zeros unchanged, giving the desired marked word.

The proof first joins the scan and writing runs, then joins that composite run to the copying run, using `Turing.rt_copy_seam` at both transitions. The component theorems provide first-arrival and head-radius bounds; throughout all three phases the active heads remain between one cell left and $|w|$ cells right of their starting positions, which implies distance at most $|w|+1$. The lengths add, including the two phase-transition steps: $(2|w|+2)+1+(2|w|+2)+1+4=4|w|+10$. Finally, the endpoint tape description is simplified by separating its first cell from the remaining cells of the zero word.

**Key facts.** `Turing.copyTM_run_ofCfg`, `Turing.scanTM_run_ofCfg`, `Turing.scanResult_map`, `Turing.writeConstTM_run_ofCfg`, `Turing.rt_copy_seam`.
