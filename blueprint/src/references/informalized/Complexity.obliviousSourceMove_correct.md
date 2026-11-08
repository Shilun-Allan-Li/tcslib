<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.obliviousSourceMove_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of virtual head movements

**Claim.** At offset zero, the virtual head directions selected from a configuration agree with the shift vector of the original machine’s totalized action.

**Proof.** First replace the selected action in the virtual movement definition by the totalized action, using correctness of the selected source action (`obliviousSourceAction_correct`), and identify the offset-zero payloads with the source reads (`sourcePayload_origin`). It remains to compare coordinates. On each work-tape coordinate, both vectors use the corresponding work-tape shift of that action. On the virtual-input coordinate, the payload tag records whether the input head is at the left boundary, the right boundary, or in the interior. At either boundary, a move pointing out of the input interval is clipped to zero; otherwise the original input movement is retained. This is exactly the clipped movement used in the source shift vector, proving agreement in all coordinates.

**Key facts.** `Complexity.obliviousSourceAction_correct`, `Complexity.sourcePayload_origin`.
