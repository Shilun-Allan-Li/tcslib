<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.mem_binaryMultiplicationTable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Multiplication Table Membership

**Claim.** For ℓ>0, a certified binary field implementation of dimension ℓ, and any x,y ∈ 𝔽₂^ℓ, the triple consisting of x, y, and their modular product belongs to the multiplication table.

**Proof.** The multiplication table is formed from every ordered pair in the list of binary vectors, mapping each pair (u,v) to (u,v,uv) using the specified modular multiplication. Both x and y belong to the list (FABL.mem_allBinaryVectors), so (x,y) is among those pairs. Its image is the stated triple, which therefore belongs to the table.

**Key facts.** `FABL.mem_allBinaryVectors`.
