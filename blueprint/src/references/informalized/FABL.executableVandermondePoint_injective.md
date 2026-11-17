<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondePoint_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Point Assignment

**Claim.** The assignment sending each index $j$ to the binary vector at position $j$ in the enumeration is injective.

**Proof.** The point assignment is the composition of the inclusion of indices from $\{0,\ldots,n-1\}$ into $\{0,\ldots,2^d-1\}$ and the enumeration equivalence from those positions to length-$d$ binary vectors. The inclusion is injective because $n\le2^d$ (`ExecutableVandermondeInput.n_le_fieldSize`), and an equivalence is injective. Their composition is therefore injective.

**Key facts.** `FABL.ExecutableVandermondeInput.n_le_fieldSize`.
