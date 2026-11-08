<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.jacInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the Jacobi invariant

**Claim.** If $z$ and $S$ satisfy the stated Jacobi invariant, then after one Jacobi step the resulting state still satisfies it for the same $z$.

**Proof.** Write $S$ as the nested encoding of $A,N,s$ supplied by the invariant. The projections of these encodings recover their components, so the Jacobi step splits into the cases $A=0$, $A$ odd, and $A$ even. If $A=0$, the step leaves the state unchanged and the existing invariant witnesses suffice. Otherwise $A>0$. When $A$ is odd, the step replaces the first component by $N\bmod A$, swaps the roles of $A$ and $N$ in the invariant witnesses, and preserves the length bounds: the remainder is represented by its binary expansion, whose length is bounded by that of $A$. The invariant says that $N$ is odd whenever the second projection of $z$ is odd; thus quadratic reciprocity applies to the two odd numbers. Its sign is negative exactly when both are $3$ modulo $4$, as detected by their second bits. The step flips the encoded sign in exactly that case, so the sign-adjusted Jacobi symbol remains the one for the projections of $z$. If the sign condition does not hold, the reciprocity factor is $1$ and no flip is needed. When $A$ is even, the step replaces it by $A/2$ and retains $N$. The new first component meets the length bound, and the sign is flipped exactly when the residue of $N$ modulo $8$ makes $(2/N)=-1$. By the even-numerator identity, $(A/N)=(2/N)(A/2/N)$; the selected sign adjustment therefore preserves the required Jacobi value. In both even cases the oddness condition on $N$ and the sign-length bound persist, establishing the invariant.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.bitsVal_mod_two`, `Complexity.BinArith.length_bits_le_of_le`, `Complexity.BinArith.mod_four_eq_three_iff`, `Complexity.BinArith.jacobiSym_odd`, `Complexity.BinArith.signOf_flipSign`, `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.jacobiSym_even`, `Complexity.BinArith.jacobiSym_two_bits`, `Complexity.BinArith.bitsVal_drop_one`.
