<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweepFold_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transduction of a Concatenation

**Claim.** Processing $as$ followed by $bs$ from state $s$ has the same final state and rewritten word as processing $as$ first and then processing $bs$ from the resulting state; the rewritten word is the concatenation of the two outputs.

**Proof.** Induct on the list $as$, allowing the initial state $s$ to vary. For the empty list, processing it leaves state $s$ and produces the empty word, so the claim reduces to the defining equation for processing $bs$. For $as=a::as'$, processing the concatenation first applies the local rule to $a$, then processes $as'++bs$ from the updated state. The induction hypothesis splits that remaining processing into $as'$ followed by $bs$, with their outputs concatenated. Reassembling the initial symbol’s output gives exactly the output from processing $as$ concatenated with the output from processing $bs$ in sequence, and the final states agree.
