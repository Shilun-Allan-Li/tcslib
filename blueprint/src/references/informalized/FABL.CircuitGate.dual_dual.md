<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.CircuitGate.dual_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involution of Gate Duality

**Claim.** For either a logical AND gate or a logical OR gate, taking the dual twice returns the original gate.

**Proof.** There are only two cases. The dual of AND is OR and the dual of OR is AND; applying the dual once more in either case returns the starting gate. The equality follows directly from these defining equations.
