<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.unaryTape_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of the Origin Marker

**Claim.** On the unary tape with $N$ markers, the origin marker occurs at position $z$ exactly when $z=0$.

**Proof.** If $z=0$, the first case in the definition of the tape assigns the origin marker. If $z\ne0$, that case does not apply; the remaining possible value is a unit marker or blank, neither of which is the origin marker. Hence the origin marker occurs exactly at zero.
