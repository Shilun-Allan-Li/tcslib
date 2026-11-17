<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_serialization_actions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialization by State Groups

**Claim.** The canonical serialization of a coded machine consists of its header followed by the serialized transition records, grouped in increasing state order, with nine records in each state group.

**Proof.** Unfold the canonical serialization and separate the initial-state unary code from the transition table. The latter is indexed by states and by the three possible input symbols and three possible work-tape symbols. Reexpress each state’s nine transition actions as a group, using the fact that the machine has one work tape: its tape-read function is determined by its value at the sole tape index. For each action, case analysis on its input movement, tape write and movement, output, and successor state shows that the action-bit encoding used by the canonical serialization is exactly the record-bit encoding. Thus the transition portion is the concatenation, state by state, of the nine serialized records, and the separated prefix is precisely the header.
