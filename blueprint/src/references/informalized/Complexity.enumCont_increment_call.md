<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_increment_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time bound for an increment call

**Claim.** Under the stated time and output hypothesis for $I$, the buffered composition started in its candidate phase reaches a halted configuration with the fixed-width increment output (using the empty word on overflow) within $(j+3)(|s|+1)$ steps.

**Proof.** The concatenation machine first copies $s$ from its work tape onto its output and halts after $|s|+1$ steps (`Complexity.enumCont_concat_candidate`, with the empty prefix and remainder $s$). Apply the prepared-composition result (`Complexity.enumCont_prepared_comp`) to this halted first-machine configuration and the computation of $I$ on input $s$. Its output is $(\operatorname{incFixed}(s)).getD\,[]$, and the assumed time bound for $I$ supplies its halting computation in $j(|s|+1)$ steps. The prepared-composition bound adds the first machine's time, the length of its output, two buffering steps, and the second machine's time. Since the first output is $s$, this is at most $(|s|+1)+|s|+2+j(|s|+1)=(j+3)(|s|+1)$. Finally, the round-seam identity (`Complexity.enumCont_round_seam`) identifies the buffered initial configuration with the specified candidate-phase configuration, giving the required state and output there.

**Key facts.** `Complexity.enumCont_concat_candidate`, `Complexity.enumCont_prepared_comp`, `Complexity.enumCont_round_seam`.
