<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.virtualMove_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of Virtual Head Movement

**Claim.** The virtual head's coordinate changes exactly as the native clamped input head does, and its updated boundary tag correctly records whether the new position is at an endpoint.

**Proof.** Consider first a configuration at the left endpoint. The tag condition forces the tag to be false. For each of the three movements, the definition of virtual movement suppresses an attempted move farther left, while the native movement is clamped there; a stationary or rightward move agrees directly. The resulting coordinate identity and tag condition follow in each case. Away from the left endpoint, split again according to whether the head is at the right endpoint. At the right endpoint the tag is true and the scanned symbol is blank: a rightward attempt is suppressed, a leftward move uses the ordinary decrement, and a stationary move preserves the position. These cases give the coordinate identity and the correct new tag. At an interior position, the scanned symbol is present, so virtual movement is just the requested movement. A stationary move preserves the tag condition; a left move decrements the position and makes the tag false, and a right move increments it and makes the tag true. The standard formulas for native movement away from the corresponding endpoint (`moveInputPos_neg_of_ne_left` and `moveInputPos_pos_of_ne_right`) establish the coordinate equality in those moving cases. The fact that an interior position scans the corresponding input symbol is supplied by `inputSymbolInner`.

**Key facts.** `Turing.moveInputPos_neg_of_ne_left`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.inputSymbolInner`.
