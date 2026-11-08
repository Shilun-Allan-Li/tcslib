<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.AgreeOutside.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexive agreement outside a set

**Claim.** Every memory agrees with itself outside any set of integer addresses.

**Proof.** At each address outside the set, the memory's value equals itself. Hence the two memories agree at every point of the complement.
