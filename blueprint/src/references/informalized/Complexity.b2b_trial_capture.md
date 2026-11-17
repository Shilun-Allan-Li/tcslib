<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_trial_capture -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity Trial Capture

**Claim.** Under the stated time and space bounds for the identity machine, the identity phase reaches a configuration storing $u$ on the first designated tape and $x$ on the second, with the third blank. It avoids the exit state before that time, and all work-head positions stay within $|x|+s$.

**Proof.** Place the identity machine’s doubled work-tape bank in the designated tape range, with the capture tape outside that range. The initial configuration has the first designated tape storing $u$, all embedded bank tapes blank, and the identity machine in its cleaning initial state. The embedding and capture-tape separation ensure that the bank starts blank and does not overwrite the buffer. The capture-shape lemma (`b2b_capture_shape`) identifies this embedded configuration with the stated trial configuration, including the tape contents and head positions.

Now apply the cleaned-simulation capture lemma (`b2b_clean_capture`) to the assumed computation of $M_I$ on $x$. It supplies a time and input-head position at which the simulation has captured output $x$, has not yet entered its exit state at any earlier time, and has obeyed the bound $|x|+s$ on every work-head position. The same capture-shape identification translates its endpoint and earlier-state condition to the trial machine’s configurations. Finally, the embedded bound transfers to all trial tapes: the buffer and other designated tapes have the explicitly tracked positions, while positions in the simulated bank satisfy the capture bound. This gives the required endpoint, exit-state avoidance, and head bound.

**Key facts.** `Complexity.b2b_capture_shape`, `Complexity.b2b_clean_capture`.
