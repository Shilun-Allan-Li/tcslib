<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# One Width-Split Round

**Claim.** Given the stipulated computations of $C$ and $D$, the combined controller completes one round in positive time within the stated bound, avoids the anchor at every intermediate positive time, and either halts with the encoded prefix and suffix when their length condition holds or returns to the anchor with the candidate advanced as specified.

**Proof.** First, one control step leaves the anchor and enters preparation, without changing the words. The preparation result provides a bounded run to preparation state $8$. Split into two cases according to whether $|w|<|s|$. If so, the preparation flag directs the controller to the erasure and finish segment with a negative verdict; that segment returns the unchanged candidate to the anchor. Joining these phases preserves anchor avoidance, and the strict inequality makes the acceptance length equation false.

If instead $|s|\le |w|$, preparation directs the controller to the width-start phase. The testing lemma runs the width and length computations on their respective banks and compares their output words, reaching the first erasure phase with verdict given by equality of those words. Its hypotheses are precisely the two assumed machine runs and their intermediate-state exclusions. The finish lemma then erases or emits according to this verdict. The binary-check fact identifies equality of the two binary representations—of $f(|s|)$ and the suffix length—with $|s|+f(|s|)=|w|$. Thus a positive verdict yields the halted output encoding the prefix and suffix; a negative verdict returns to the anchor with the candidate updated according to the stipulated split rule.

In both cases, the controller's phase segments are joined using the run-addition law. The safety-joining results propagate avoidance of the anchor across the segments, while the strict joining result handles the initial departure and the final interval of strictly intermediate times. The preparation, testing, and finish time bounds, together with the lengths of the binary output words, give the stated total bound; the chosen total time is positive because it includes the initial control step and subsequent phase transitions.

**Key facts.** `Turing.FinTM.emitterP2_control`, `Turing.FinTM.emitterP2_words_clean`, `Turing.FinTM.emitterP2_body_prepare`, `Turing.FinTM.emitterP2_after`, `Turing.FinTM.emitterP2_body_finish`, `Turing.FinTM.emitterP2_strict_join`, `Turing.FinTM.emitterP2_body_test`, `Turing.FinTM.splitSafe_join`, `Turing.FinTM.emitter_binary_check`, `Turing.MultiTapeTM.runFrom_add`.

**Caveat.** The proof source relies on the preparation, testing, and finish lemmas for detailed time bounds and machine behavior; their full statements are only partially supplied here. The overall assembly and case split are clear, but these intermediate estimates cannot be independently checked from the supplied upstream statements.
