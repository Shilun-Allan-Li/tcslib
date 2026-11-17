<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.jacobiSymZMod_natCast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Jacobi Symbol on Natural Casts

**Claim.** For every positive natural number $N$ and natural number $A$, the Jacobi symbol modulo $N$ at the residue class of $A$ equals the residue class of the integer Jacobi symbol of $A$ and $N$.

**Proof.** The residue class of $A$ has canonical representative equal to the remainder of $A$ modulo $N$. By definition, the Jacobi symbol modulo $N$ applies the integer Jacobi symbol to that representative. Periodicity of the Jacobi symbol in its first argument modulo $N$ identifies this with the Jacobi symbol of $A$ itself. Reducing the result modulo $N$ gives the stated equality.
