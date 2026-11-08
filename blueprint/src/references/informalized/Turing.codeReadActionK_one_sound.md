<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeReadActionK_one_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Tape Action Reader Soundness

**Claim.** Whenever reading a bit string as a one-work-tape action succeeds with result $(a,r)$, the input is the serialization of $a$ followed by $r$.

**Proof.** The general action-reader soundness theorem says that a successful read with any number of work tapes recovers the input as the $k$-tape action encoding followed by the remaining string (`Turing.codeReadActionK_sound`). Apply it with $k=1$ to obtain $x=\mathrm{actionBitsK}(a)\mathbin{++}r$. For a one-work-tape action, the general encoding agrees with the one-tape encoding (`Turing.actionBits_eq_actionBitsK`), so substitution gives $x=\mathrm{actionBits}(a)\mathbin{++}r$.

**Key facts.** `Turing.actionBits_eq_actionBitsK`, `Turing.codeReadActionK_sound`.
