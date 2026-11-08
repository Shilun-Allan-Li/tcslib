<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.ao_move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Head Advance of the Advice Machine

**Claim.** If the machine's transition on the bit at position $i$ moves to state $q'$, then one step from the specified configuration gives the configuration in state $q'$ with input head at position $i+2$.

**Proof.** The one-step transition lemma identifies the step with the action prescribed on the current bit (\texttt{Complexity.ao_step}); the hypotheses identify that bit as $v$ and that action as the move to $q'$. The move action preserves the empty work tapes and output, changes the state to $q'$, and advances the input head by one. Since the starting head position is $i+1$, the new position is $i+2$. The configuration extensionality principle for machines with zero work tapes reduces equality to state, input-head position, and output (\texttt{Turing.Cfg.ext_zero_tapes}); the head-position identity follows from the positive-move rule away from the right boundary (\texttt{Turing.moveInputPos_pos_of_ne_right}).

**Key facts.** `Complexity.ao_step`, `Turing.Cfg.ext_zero_tapes`, `Turing.moveInputPos_pos_of_ne_right`.
