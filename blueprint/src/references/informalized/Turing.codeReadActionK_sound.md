<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeReadActionK_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action Reader Soundness

**Claim.** Whenever reading a bit string as a $k$-work-tape action succeeds with result $(a,r)$, the input is the serialization of $a$ followed by $r$.

**Proof.** Unpack the successful action read into four successive successful reads: the input-head movement, the vector of work-tape actions, the output bit, and the next state. The returned action and suffix are exactly those produced by the final construction.

The movement reader soundness theorem identifies the initial segment as the movement code followed by the next intermediate suffix (`Turing.codeReadSign_sound`). For the work tapes, apply the vector-reader soundness theorem, using work-reader soundness for each tape: it serializes the optional write and movement of that tape and passes on the next suffix (`Turing.codeReadWork_sound`, `Turing.codeReadVec_sound`). The output and state reader soundness theorems then identify their respective segments (`Turing.codeReadOutput_sound`, `Turing.codeReadState_sound`). Concatenating these segments in their read order yields precisely the action encoding, followed by $r$.

**Key facts.** `Turing.codeReadSign_sound`, `Turing.codeReadVec_sound`, `Turing.codeReadWork_sound`, `Turing.codeReadOutput_sound`, `Turing.codeReadState_sound`.
