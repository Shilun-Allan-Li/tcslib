<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.gateCoordinate_ne_inputCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input and Gate Coordinates Are Distinct

**Claim.** For a Boolean circuit on $n$ input bits, every gate coordinate differs from every input coordinate.

**Proof.** Under the standard identification of a coordinate in the disjoint union of the input indices and gate indices with a coordinate in $	ext{Fin}(n+C.	ext{gateCount})$, a gate coordinate comes from the right summand and an input coordinate from the left summand. If these coordinates were equal, injectivity of that identification would force the two summand elements to be equal, which is impossible because they lie in different summands.
