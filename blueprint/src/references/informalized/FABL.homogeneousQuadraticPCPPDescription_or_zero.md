<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.homogeneousQuadraticPCPPDescription_or_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic System PCPP Dichotomy

**Claim.** For a homogeneous quadratic system in $n$ variables, either $n=0$ and the system is satisfied by every Boolean word or by none, or $n$ is positive and the system has an associated PCPP description.

**Proof.** Split on whether $n=0$. If so, the zero-dimensional dichotomy says that every word satisfies the system or that no word does (\texttt{isBoolHomogeneousQuadraticSystem\_zero\_universal\_or\_empty}); this gives the first alternative. If $n\ne0$, then $n$ is positive, so it has a nonzero witness. The construction theorem for the homogeneous quadratic PCPP supplies a description for this system at that positive dimension, yielding the second alternative.

**Key facts.** `FABL.isBoolHomogeneousQuadraticSystem_zero_universal_or_empty`.

**Caveat.** The proof invokes the PCPP construction theorem as a black box; it does not establish its query count, proof length, or rejection rate here.
