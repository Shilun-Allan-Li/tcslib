<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependence.lean :: FABL.f₂Support_nonempty_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty support criterion

**Claim.** The support of $\gamma\in\mathbb F_2^n$ is nonempty exactly when $\gamma$ is not the zero vector.

**Proof.** If the support is nonempty, it contains a coordinate where $\gamma$ is nonzero, so $\gamma$ cannot be the zero vector. Conversely, if the support were empty, every coordinate of $\gamma$ would be zero. Hence $\gamma$ would equal the zero vector, contradicting the assumption that it is nonzero. Therefore its support is nonempty.
