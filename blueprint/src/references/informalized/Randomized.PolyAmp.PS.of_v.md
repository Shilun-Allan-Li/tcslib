<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.PS.of_v -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Vector Invariance

**Claim.** If a vector is the register vector encoded by a given record, then initializing the polynomial-amplification program with that vector preserves the record's termination and probability properties.

**Proof.** The assumed equality identifies the vector $f$ with the vector encoded by $\sigma'$. Rewriting the initial configuration using this equality makes it exactly the configuration in the assumed semantic property. Thus that property, including termination and the two probability identities, holds for the initialization with $f$.
