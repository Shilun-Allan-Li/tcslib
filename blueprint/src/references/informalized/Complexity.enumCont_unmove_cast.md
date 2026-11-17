<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_unmove_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Move Displacement

**Claim.** For each head move $d\in\{-1,0,1\}$, encoding it as a tape symbol and decoding that symbol gives a move whose integer displacement is the negative of the displacement of $d$.

**Proof.** There are three possible moves. For the negative move, encoding gives `some false`, which decodes to the positive move; their integer displacements are $1$ and $-1$. For the zero move, encoding gives `none`, which decodes to zero, its own negative. For the positive move, encoding gives `some true`, which decodes to the negative move; their displacements are $-1$ and $1$. Thus the claimed identity holds in every case.
