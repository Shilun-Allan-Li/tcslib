<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_repeat_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Word Generation by a Counter Loop

**Claim.** The repeat machine writes $s$ consecutive copies of `pat` to tape 1, advances that tape’s head by exactly $s|\mathrm{pat}|$, and reaches its final phase at the specified time without reaching it earlier or exceeding the stated head displacement.

**Proof.** First run the copy machine from tape 0 to tape 2. By `Turing.copyTM_run_ofCfg`, after $2|ws|+2$ steps tape 2 contains the counter word, and the run has not reached its copy exit earlier. The blank-tape hypothesis on tape 2 ensures its boundary cells are blank, so the copied counter has the required buffer interpretation. Apply the repeat-expansion theorem (`Turing.rt_expand_run`) to tape 2. The value hypothesis identifies the represented counter with $s$; the theorem says the expansion writes $s$ copies of `pat` to tape 1, advances its head by $s|pat|$, and takes $s(|pat|+1)+\mathrm{counterOverhead}(ws,s+1)$ steps, with its first-exit and head bounds. During this expansion tape 2 is changed to an all-true word, as recorded in the intermediate configuration.

The proof then applies `Turing.clearTM_run_ofCfg` to that all-true word on tape 2. It takes $2|ws|+2$ steps and clears that word; the blank boundary condition needed for this application follows from the original blank-tape assumption. The seam-composition theorem (`Turing.rt_copy_seam`) joins the expansion and clearing stages, and then joins their result to the initial copy stage. The component bounds imply that every head remains within $s|pat|+|ws|+1$ of its original position; the intermediate shift of tape 1 is accounted for when applying the later bounds. Adding the stage durations and the two phase transitions gives $2|ws|+2+1+s(|pat|+1)+\mathrm{counterOverhead}(ws,s+1)+1+2|ws|+2$, equal to the stated $t$. At that endpoint the cleared counter tape restores its original contents, while tape 1 retains the generated word and the advanced head position. Configuration extensionality gives the claimed final record; the seam theorem also supplies the no-earlier-exit property.

**Key facts.** `Turing.copyTM_run_ofCfg`, `Turing.rt_expand_run`, `Turing.clearTM_run_ofCfg`, `Turing.rt_copy_seam`.
