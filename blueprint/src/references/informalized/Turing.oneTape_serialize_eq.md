<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.oneTape_serialize_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of one-tape serializations

**Claim.** For every machine $M$ in code normal form, its canonical serialization agrees with the $k$-work-tape serialization of its underlying machine specialized to one work tape.

**Proof.** Expand both serialization definitions. The one-tape machine's table enumerates its states, input symbols, and the three possible symbols read on its sole work tape; the general table does the same using the one-tape read enumeration. These read enumerations agree (Turing.workReadsK_one). For each resulting transition, the action encoding in the one-tape format agrees with the general action encoding specialized to one tape (Turing.actionBits_eq_actionBitsK). Substituting these equalities into the table constructions leaves identical lists, and the common state prefix and pair encoding then give equality of the full serializations.

**Key facts.** `Turing.workReadsK_one`, `Turing.actionBits_eq_actionBitsK`.
