<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.jacobiSym_two_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Jacobi Symbol from Two Bits

**Claim.** For an odd represented integer, the Jacobi symbol $(2/N)$ is $-1$ when bits two and three differ, and $1$ when they agree, with missing bits treated as $0$.

**Proof.** The formula for the Jacobi symbol with numerator $2$ identifies it with the value of the mod-$8$ character at the represented integer. The represented integer modulo $8$ is determined by its first three bits: it is the first bit plus twice the second bit plus four times the third bit. Since the integer is odd, the first bit is $1$. Thus the residue is $1$, $3$, $5$, or $7$ according to the two remaining bits. The mod-$8$ character takes value $1$ on residues $1$ and $7$, and $-1$ on residues $3$ and $5$; these cases are exactly when the second and third bits agree or differ, respectively. The identity for the residue modulo $8$ is `bitsVal_mod_eight`; the finite case check also covers missing bits through the convention that `headD false` returns false.

**Key facts.** `Complexity.BinArith.bitsVal_mod_eight`.
