<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arCoords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block Coordinates of a Tape Position

**Claim.** For $p=(N+1)z+j$ with $0\le j\le N$, division by $N+1$ gives quotient $z$ and remainder $j$.

**Proof.** The Euclidean division uniqueness theorem for integers says that a representation of an integer as $r+(N+1)z$, with $0\le r<N+1$, determines its quotient and remainder. Here $j$ satisfies those bounds because it is a `Fin (N+1)` value, and $p=j+(N+1)z$. Thus the quotient is $z$ and the remainder is $j$. The remainder, viewed as a natural number and then as a bounded index, is exactly the given offset.
