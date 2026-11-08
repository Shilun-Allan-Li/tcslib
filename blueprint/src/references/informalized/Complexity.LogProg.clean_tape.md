<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean :: Complexity.LogProg.clean_tape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cleaning One Tape

**Claim.** Under the stated interval, support, marking, and head-bound hypotheses, the cleaning machine erases the selected tape and its auxiliary marks, returns the corresponding heads to the origin, advances to the next cleaning state, and keeps every head within the bound throughout.

**Proof.** First, the marking-stage transition leaves the data tape unchanged and writes the auxiliary marking pattern for the interval $[a,b]$. The equality relating the updated marking tape to the prescribed marker pattern follows from the hypothesis about writing at the scanned cell and from the transition's tape action (`ccfg_mark`, `apply_clAct`).

In the go-right phase, the machine moves to just beyond $b$; the interval's right margin ensures this position remains within the bound. The phase-run result establishes both that head bound throughout and that the machine arrives at $b$ in the erasing phase (`goR_run`). Next it erases the original data tape while moving left across the interval, removing the auxiliary marks as it goes. The support hypothesis ensures no nonblank data remains outside $[a,b]$; below $a$, the tape is therefore blank. The erasing-run result gives the bound throughout and places the machine at $a$ with the remaining marker at $a$ (`erase_run`). Its endpoint uses the update-preservation bound (`abs_update_le`).

Finally, the back phase moves right from $a$ to the origin marker, removes that marker, and advances to the next tape's marking state (or halts if there is no next tape). The back-run result bounds this phase and returns the relevant heads to zero (`back_run`); the additional head update remains bounded by `abs_update_le`. The run is the concatenation of the initial marking step and these three phase runs. The composition lemma preserves the head bound across these time intervals (`runFrom_forall_append`), and the run-composition law identifies the final configuration (`Turing.MultiTapeTM.runFrom_add`). The stated endpoint follows by the tape and head updates, with the other tapes and the input and output unchanged.

**Key facts.** `Complexity.LogProg.ccfg_mark`, `Complexity.LogProg.apply_clAct`, `Complexity.LogProg.goR_run`, `Complexity.LogProg.abs_update_le`, `Complexity.LogProg.erase_run`, `Complexity.LogProg.back_run`, `Complexity.LogProg.runFrom_forall_append`, `Turing.MultiTapeTM.runFrom_add`.
