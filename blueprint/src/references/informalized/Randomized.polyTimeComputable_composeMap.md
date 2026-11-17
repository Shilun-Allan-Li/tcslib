<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.polyTimeComputable_composeMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Closure Under Composition Map

**Claim.** For fixed natural parameters and any polynomial-time computable $f$, the described composition map on bit strings is polynomial-time computable.

**Proof.** The first stage, `sliceTake` with parameters $a_1,k_1$, forms the pair from the decoded first component and the prefix of the decoded second component of the specified length. This stage is polynomial-time computable. Composing it with $f$ remains polynomial-time computable by closure under composition. In parallel, `sliceDrop` with the same parameters computes the remaining suffix, and extracting the second component of its encoded result is polynomial-time computable. Pairing this suffix with the output of $f$ is polynomial-time computable by closure under pair encoding. Finally, applying `sliceTake` with parameters $a_2,k_2$ is again polynomial-time computable. These stages are exactly the prescribed procedure, including the empty-component behavior inherited from the decoders.

**Key facts.** `Randomized.polyTimeComputable_sliceTake`, `Complexity.PolyTimeComputable.comp`, `Randomized.polyTimeComputable_sliceDrop`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.pairEncode`.
