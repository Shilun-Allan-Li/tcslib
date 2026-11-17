<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPGaps.lean :: FABL.BooleanCircuit.not_satisfiable_iff_unsatisfiable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unsatisfiability and satisfiability

**Claim.** A Boolean circuit has no satisfying input assignment if and only if it is unsatisfiable, meaning that every input assignment fails to make it output true.

**Proof.** By definition, satisfiability means that there exists an input assignment accepted by the circuit. Its negation says that no such assignment exists. This is exactly the definition of unsatisfiability.
