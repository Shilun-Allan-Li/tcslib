<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.tableauCircuit_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Input Tableau Circuit

**Claim.** For every finite-state Boolean-input machine $M$ and natural numbers $n,T$, the tableau circuit is well formed and every gate reads at most two input vertices.

**Proof.** We prove by induction on the number of tableau time blocks that every gate in the block list has distinct arguments, satisfies the required single-input condition for a NOT gate, and has at most two arguments. At time zero the only gates are the two constant gates; they have no arguments, so all three properties hold. At the successor stage, gates inherited from the preceding block retain these properties by induction. Every newly appended gate belongs to the embedding of one of the tableau gadgets. The embedding lemma says that if each gadget circuit is well formed and has fan-in at most two, then all gates produced by embedding the list have distinct arguments, meet the NOT condition, and have fan-in at most two (BoolCircuit.faninTwo_embedAll). Each tableau gadget is a gadget for a Boolean function, and every such gadget is well formed with fan-in at most two (BoolCircuit.gadget_isFaninTwo). Thus the properties hold for every gate at every stage. The well-formedness of the full tableau circuit follows from the first two properties for its gates, and the fan-in bound follows from the third.

**Key facts.** `BoolCircuit.faninTwo_embedAll`, `BoolCircuit.gadget_isFaninTwo`.
