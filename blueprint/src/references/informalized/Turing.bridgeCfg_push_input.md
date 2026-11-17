<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeCfg_push_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Push with an Input Head Move

**Claim.** The two actions that move the selected work-tape head left and then write $a$ while moving the input head by $d$ produce the configuration with state $q'$, input position moved from $p$ by $d$, unchanged output, and stack assignment updated by prepending $a$ to $st(k)$.

**Proof.** First apply the lemma describing a push on a bridge tape: moving the selected work-tape head left and writing $a$ leaves the input position fixed and changes the stack assignment to $\operatorname{update}(st,k,a::st(k))$ (`Turing.bridgeCfg_push`). The second action has the same work-tape behavior, but its input-head movement is $d$. By the definition of configuration update, its new input position is therefore the clamped move of $p$ by $d$. Its state becomes $q'$, while the stack contents and output remain as established by the first action. Comparing the state, input position, work tapes, work-tape head positions, and output gives the claimed configuration.

**Key facts.** `Turing.bridgeCfg_push`.
