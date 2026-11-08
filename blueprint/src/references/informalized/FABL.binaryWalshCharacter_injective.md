<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/ParityBasis.lean :: FABL.binaryWalshCharacter_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Walsh characters

**Claim.** For every $n\ge0$, distinct subsets $S,T\subseteq\{0,\ldots,n-1\}$ define distinct Walsh characters on $\mathbb F_2^n$; equivalently, the map sending each subset to its character is injective.

**Proof.** Suppose the characters associated with $S$ and $T$ are equal. Fix a coordinate $i$ and evaluate both characters on the vector that is $1$ at $i$ and $0$ at every other coordinate. The coordinate sum over a subset is then $1$ precisely when that subset contains $i$, and is $0$ otherwise. The binary sign character takes these two values to $-1$ and $1$, respectively. Equality of the evaluated characters therefore implies that $i$ belongs to $S$ exactly when it belongs to $T$. Since this holds for every coordinate, the subsets are equal, proving injectivity.
