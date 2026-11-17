<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.gcdInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Gcd Invariant and Measure Decrease

**Claim.** A gcd step preserves the gcd invariant, strictly decreases the measure whenever it is positive, and fixes the state whenever its measure is zero.

**Proof.** Write the invariant state as $S=\langle x,y\rangle$, with $|x|,|y|\le |z|$ and the stated equality of gcds. The projections of this encoding are exactly $x$ and $y$ (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`). If $V(y)=0$, the step fixes $S$, so the invariant and the zero-measure implication hold immediately; in this case the measure is just the size of $V(x)V(y)=0$, hence cannot be positive.

Now suppose $V(y)>0$. The step encodes $y$ together with the binary expansion of $V(x)\bmod V(y)$. The remainder is at most $V(x)$, so its binary word has length at most $|z|$ by the binary-expansion length bound (`Complexity.BinArith.length_bits_le_of_le`). Its represented value is the remainder (`Complexity.LogProg.bitsVal_bits`). The gcd is unchanged by replacing $(V(x),V(y))$ with $(V(y),V(x)\bmod V(y))$: this follows from the Euclidean gcd identity, using symmetry and the recursive gcd formula. Thus the new encoding satisfies the invariant.

For the measure decrease, the new second value is the remainder, which is less than $V(y)$. Hence the new correction term is zero. If $V(x)<V(y)$, the remainder is $V(x)$, and the old correction term was one; swapping the two factors leaves their product unchanged, so the measure drops by one. Otherwise $V(y)\le V(x)$. The old correction term is zero, and the quotient is at least one. The division identity then gives $2(V(x)\bmod V(y))\le V(x)$, so the new product is at most half the old positive product. The binary size therefore strictly decreases by the size-halving bound (`Complexity.BinArith.size_lt_of_two_mul_le`). Finally, if the original measure is zero, its binary-size term must be zero, so the product is zero; the correction term must also vanish, since it is nonnegative. Thus one of $V(x),V(y)$ is zero. The positive-$V(y)$ case would then have $V(x)=0$ and the correction term vanishing, but the step's remainder is also zero; more directly, the proof's case split rules out $V(x)<V(y)$ from the zero measure and product zero, and the remaining branch forces the unchanged-state conclusion as encoded by the proof's arithmetic. Therefore the step fixes $S$.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.length_bits_le_of_le`, `Complexity.BinArith.size_lt_of_two_mul_le`.

**Caveat.** The final zero-measure subcase in the supplied proof uses arithmetic automation after deriving that the product is zero and that the correction term vanishes. The written argument does not fully justify why the positive-second-value branch must fix the state; in fact, with $V(x)=0<V(y)$, the step generally changes the encoding. The claim may not follow from the displayed definitions.
