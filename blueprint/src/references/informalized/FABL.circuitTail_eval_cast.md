<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.circuitTail_eval_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under an Index Cast

**Claim.** Transporting a circuit tail along an equality of its index sizes preserves evaluation: evaluating the transported tail on $v$ agrees with evaluating the original tail on the assignment obtained by casting indices along that equality.

**Proof.** Substitute the equality of the two index sizes. The transport then becomes the identity, and casting an index along the reflexive equality leaves it unchanged. Both sides are therefore the same evaluation of the tail on $v$.
