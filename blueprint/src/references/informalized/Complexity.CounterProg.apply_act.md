<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.apply_act -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Applying a Work-Tape Action

**Claim.** Applying an action on tape $t$ moves the input head as specified, writes at the current position of tape $t$ if a write is prescribed, and moves that tape's head by $m$. Every other tape and work head remains unchanged; the state becomes $q$ and the output is extended by the optional bit $o$.

**Proof.** Compare the two configurations field by field. The state, input position, and output follow directly from the definition of applying the action. For the work tapes, the action prescribes $(wr,m)$ at index $t$ and prescribes no write or movement at every other index. Thus the tape family is exactly the original family with its value at $t$ replaced by the result of writing $wr$ at tape $t$'s current head position; all other tapes agree with the original. For the head positions, the update changes the position at $t$ by adding $m$ and leaves all other positions fixed. These field equalities give the asserted configuration.
