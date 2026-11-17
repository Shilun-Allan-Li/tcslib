<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.mem_binaryAdditionTable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Addition Table Membership

**Claim.** For every nonnegative integer ℓ and every x,y ∈ 𝔽₂^ℓ, the triple (x,y,x+y) belongs to the binary addition table.

**Proof.** By definition, the table is obtained by taking every ordered pair from the list of binary vectors and mapping each pair (u,v) to (u,v,u+v). Every binary vector belongs to that list (FABL.mem_allBinaryVectors), so (x,y) is one of the pairs. Its image is exactly (x,y,x+y), proving the claimed membership.

**Key facts.** `FABL.mem_allBinaryVectors`.
