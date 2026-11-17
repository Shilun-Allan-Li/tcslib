<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.clockTape_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unique Origin on the Captured Tape

**Claim.** For every Boolean word $w$ and integer coordinate $z$, the captured clock tape has the origin marker at $z$ if and only if $z=0$.

**Proof.** If $z=0$, the defining first branch of the captured clock tape supplies the origin marker. If $z\ne 0$, the tape instead contains either a bit symbol, when the buffer has a value, or blank, when it does not. Neither is the origin marker. Therefore the origin marker occurs exactly at coordinate $0$.
