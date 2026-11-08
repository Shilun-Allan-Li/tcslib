<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.fourierCoeff_tribes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of tribes

**Claim.** The Fourier coefficient of the tribes function has the stated empty-set value when $T$ is empty, and the stated expression in terms of its support size and cardinality when $T$ is nonempty.

**Proof.** Split according to whether $T$ is empty. In the empty case, the empty-frequency formula gives $2(1-2^{-w})^s-1$ (`FABL.fourierCoeff_tribes_empty`). In the nonempty case, the nonempty-frequency formula gives the claimed expression (`FABL.fourierCoeff_tribes_of_ne_empty`). These are exactly the two branches of the result.

**Key facts.** `FABL.fourierCoeff_tribes_empty`, `FABL.fourierCoeff_tribes_of_ne_empty`.
