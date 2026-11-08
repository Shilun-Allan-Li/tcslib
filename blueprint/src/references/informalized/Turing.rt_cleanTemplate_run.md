<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_cleanTemplate_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean-Template Machine Run

**Claim.** If the source tape initially stores the joined fields $u,v$ in the prescribed alignment and the machine starts in its sweep entry state, then after exactly $3|u|+2|v|+9$ steps it reaches its exit state, has cleared the source tape, and has moved the source head to $h-|u|-1$. The exit is avoided earlier, and all heads remain within distance $|u|+|v|+2$ of their initial positions throughout.

**Proof.** Regard the initial state as the entry state of the first clearing pass. The field-location identity (`fieldsTape_field`) identifies the portion encoding $v$ as a buffer relative to the current head. The clearing-run theorem (`clearTM_run_ofCfg`) clears that field and reaches its exit after $2|v|+2$ steps, with the stated intermediate head control. The machine next backs over the separator and the field $u$; the aligned buffer description and the backward-skip theorem (`skipBackTM_run_ofCfg`) show that this takes $|u|+3$ steps and places the head at the beginning of $u$. A final clearing pass over $u$ takes $2|u|+2$ steps by the same clearing theorem. The three phases are joined in their execution order using the run-seam theorem (`rt_copy_seam`), which combines their exact endpoints, earlier-exit properties, and head bounds. Including the one-step state transitions at the seams, the total is $(2|v|+2)+1+(|u|+3)+1+(2|u|+2)=3|u|+2|v|+9$. The final tape equality follows because both fields have been cleared and the source head ends at the start of $u$; the joined-field layout identity ensures that no residual field symbol remains. The per-phase head bounds combine to the claimed radius.

**Key facts.** `Turing.fieldsTape_field`, `Turing.clearTM_run_ofCfg`, `Turing.skipBackTM_run_ofCfg`, `Turing.rt_copy_seam`.
