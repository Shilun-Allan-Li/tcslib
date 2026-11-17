<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Primality.lean :: Randomized.polyTimeComputable_liarRound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Liar-Round Test

**Claim.** The function returning the singleton list containing the liar-round test result on an input bit string is polynomial-time computable.

**Proof.** Decode the first component as $N$. It is polynomial-time computable, as is $N_1$, obtained by subtracting one from $N$ through the unary subtraction procedure. Next form $A$ by taking the second decoded component modulo $N_1$ and adding one; composition and pair encoding show that this value is polynomial-time computable. The first Boolean test compares the gcd of $A$ and $N$ with one, using the polynomial-time gcd and equality procedures. The second compares the Jacobi-modular computation on $(A,N)$ with the modular power computation using $A$, the tail of $N_1$, and $N$; these inputs are polynomial-time assembled, and both arithmetic procedures and the equality test are polynomial-time computable. The conjunction closure combines the two singleton Boolean outputs into the singleton containing their conjunction, which is precisely the liar-round result.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.BinArith.polyTimeComputable_sub`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_mod`, `Complexity.BinArith.polyTimeComputable_add`, `Complexity.BinArith.polyTimeComputable_gcd`, `Complexity.BinArith.polyTimeComputable_beq`, `Complexity.BinArith.polyTimeComputable_jacobiModAlg`, `Complexity.BinArith.polyTimeComputable_powMod`, `Complexity.polyTimeComputable_tail`, `Complexity.polyTimeComputable_and`.
