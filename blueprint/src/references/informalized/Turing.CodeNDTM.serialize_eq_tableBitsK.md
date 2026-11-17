<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean :: Turing.CodeNDTM.serialize_eq_tableBitsK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialization by Transition Tables

**Claim.** For every machine $M$ in code normal form, its serialization is the pairing of the binary representation of its state bound with the unary encoding of its initial state followed by the two transition tables, in order: the table for choice $0$ and then the table for choice $1$. Each table lists the actions for all states, input readings, and work-tape readings.

**Proof.** The serialization is defined by enumerating both nondeterministic choices and, within each choice, all states and possible input and work-tape readings, recording the corresponding action bits. The two-choice table expansion identity (`Turing.tableBitsK_two`) rewrites this enumeration as the table for choice $0$ followed by the table for choice $1$. The action-bit identity for two work tapes (`Turing.actionBits₂_eq_actionBitsK`) identifies each recorded action with the general action encoding used in those tables. Substituting these identities into the serialization definition gives the stated pair encoding, with the unary initial-state code followed by the two tables in the required order.

**Key facts.** `Turing.tableBitsK_two`, `Turing.actionBits₂_eq_actionBitsK`.
