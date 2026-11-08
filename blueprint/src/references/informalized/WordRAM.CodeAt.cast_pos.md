<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.CodeAt.cast_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Changing Code Position Notation

**Claim.** If a list of instructions is a prefix of the part of a program beginning at position $\mathrm{pos}$, and $\mathrm{pos}=\mathrm{pos}'$, then it is also a prefix of the part beginning at $\mathrm{pos}'$.

**Proof.** The two positions are equal, so substituting $\mathrm{pos}'$ for $\mathrm{pos}$ in the given prefix relation gives the desired statement.
