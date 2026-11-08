<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.addressRecursiveNAND_even_eq_iteratedTribes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-depth NAND and iterated tribes

**Claim.** For every $k$ and every assignment of signs to the quaternary addresses of depth $k$, the depth-$2k$ recursively composed two-input NAND function, with inputs identified by pairing successive binary address digits, equals the depth-$k$ iterated two-by-two tribes function.

**Proof.** Proceed by induction on $k$. At $k=0$, both functions return the sole input sign. For the inductive step, expand the outer two levels of the depth-$2(k+1)$ NAND construction. This gives an outer NAND whose two inputs are NANDs, each applied to two depth-$2k$ subtrees. By the induction hypothesis, each of the four subtrees equals the corresponding depth-$k$ iterated tribes function, with its first quaternary digit fixed to one of the four pairs of binary digits. The resulting expression is exactly the two-level NAND on those four values. The fact that this two-level NAND is the two-by-two tribes function (`FABL.nandPair_two_levels_eq_tribes`) identifies it with the next iterated tribes level, as required.

**Key facts.** `FABL.nandPair_two_levels_eq_tribes`.
