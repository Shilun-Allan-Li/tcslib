<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBiasMarginals.lean :: FABL.coordinateProjectionLinear_coordinateExtension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection after coordinate extension

**Claim.** Extending a function on the positions of a coordinate set by zero outside that set, then projecting onto the set, recovers the original function.

**Proof.** Fix a position in the smaller coordinate cube and evaluate the projected extension there. The projection selects the corresponding coordinate in the original set, and the extension assigns that coordinate exactly the given function value. Thus the two functions agree at every position.
