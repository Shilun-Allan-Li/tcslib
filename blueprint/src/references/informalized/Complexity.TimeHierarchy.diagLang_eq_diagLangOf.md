<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.TimeHierarchy.diagLang_eq_diagLangOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Diagonal Languages

**Claim.** For every function $g$, the language defined by failure of the diagonal simulation to halt at time $g(|x|)$ with output $1$ equals the language defined by that same failure condition for the diagonal simulation machine.

**Proof.** By definition, both languages contain exactly those words $x$ for which `diagSim` does not compute the single-bit output $1$ in time $g(|x|)$. Hence their membership conditions agree for every word, so the languages are equal by extensionality; in the formal proof this is definitional equality.
