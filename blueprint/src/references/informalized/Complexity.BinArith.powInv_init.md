<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.powInv_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Power Invariant

**Claim.** The initial state formed from the decoded components of $z$ satisfies the power invariant, including its encoding, length, canonical-form, and modular-arithmetic conditions.

**Proof.** Write $A$ for the first projection of $z$, $N$ for the first projection of its second projection, and $B$ for the second projection of that second projection. The initial state encodes $B$, then $N$, then the binary representations of $A\bmod B$ and $1\bmod B$. Choose these as the invariant's exponent and two residues. The pair-encoding projection identities show that this is exactly the specified state encoding. Both residues are canonical because they are produced by the natural-number bit representation, whose value recovers the represented number. For the length bounds, if $\langle B\rangle=0$, both remainders are zero and the bit-representation length bound gives the required estimates. If $\langle B\rangle>0$, the bound on the length of a represented remainder gives the respective estimates directly. Finally, for positive $\langle B\rangle$, each remainder is strictly less than $\langle B\rangle$. The defining congruence follows by multiplying the congruence expressing $1\bmod B$ by the congruence expressing $A\bmod B$ raised to the exponent $N$; the product is congruent to $A^N$ modulo $B$.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.length_bits_bitsVal_le`, `Complexity.BinArith.length_bits_mod_le`.
