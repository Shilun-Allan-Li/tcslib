<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribes_eq_and_of_restTrue_othersFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes under block conditions

**Claim.** If every block other than the block containing coordinate $i$ has AND value $+1$, then the tribes value equals the AND value of the block containing $i$.

**Proof.** Write $p$ for the block containing $i$. The tribes output is $+1$ exactly when every block has AND value $+1$. Indeed, if every block has value $+1$, their OR is $+1$; conversely, an OR value of $+1$ forces every block value to be $+1$. Under the hypothesis on the other blocks, this condition is equivalent to the block at $p$ having value $+1$. If that block has value $+1$, both sides of the claimed equality are $+1$. Otherwise its value is $-1$, since an AND of signs must be one of $+1$ and $-1$; then not every block has value $+1$, so tribes is $-1$ as well. The stated condition on the individual coordinates within the distinguished block is not needed in this argument.
