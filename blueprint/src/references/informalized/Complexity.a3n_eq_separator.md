<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_eq_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separator Recognition

**Claim.** When the input has the form $pre\,0\,1\,v$, the parser starting at the first separator bit moves to the next input position in one step and, after the second step, is in rewind state at input position $|pre|+3$, with the decoded work word unchanged and the work head at $|u|-1$.

**Proof.** The first input position under consideration contains the first separator bit, $0$, by the interior-position input-symbol fact (`Turing.inputSymbolInner`). In parser state, the transition on $0$ moves right, leaves the work tape and its head unchanged, and enters parser state again. Thus after one step the input head is at $|pre|+2$, the work head remains at $|u|$, and the configuration is the specified intermediate one. At that next position the input symbol is the second separator bit, $1$, again by `Turing.inputSymbolInner`. The parser transition on $1$ moves the input head right, moves the work head left by one, preserves the tape, and enters rewind state. Consequently the input head is at $|pre|+3$ and the work head at $|u|-1$, as claimed. The two unfoldings of the run use the facts that a run of one more step is a step after the preceding run (`Turing.MultiTapeTM.runFrom_succ_eq_step`), and that a run of zero steps returns the starting configuration (`Turing.MultiTapeTM.runFrom_zero`). Each input-head advance is by one, using `Turing.moveInputPos_pos_of_ne_right`; the tape remains the buffer encoding of $u$ throughout.

**Key facts.** `Turing.inputSymbolInner`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_pos_of_ne_right`.
