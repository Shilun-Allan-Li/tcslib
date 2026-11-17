<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.length_binaryOperationTable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary operation table length

**Claim.** For any finite list $E$ of binary vectors and any binary operation on those vectors, the list of triples indexed by ordered pairs from $E$ has length $|E|^2$.

**Proof.** The table is obtained by mapping one triple to each ordered pair in the Cartesian product of the list with itself. Mapping a list preserves its length, and the product of a list with itself has length equal to the product of the two list lengths. Thus the table has length $|E|\cdot|E|=|E|^2$.
