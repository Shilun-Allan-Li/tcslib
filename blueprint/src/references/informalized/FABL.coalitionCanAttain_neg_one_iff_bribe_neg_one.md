<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionCanAttain_neg_one_iff_bribe_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attaining Minus One by a Coalition

**Claim.** For a monotone function, there is an input agreeing with $x$ outside $J$ on which the function equals $-1$ if and only if setting every coordinate in $J$ to $-1$ makes the function equal $-1$.

**Proof.** Suppose first that a witness $y$ agrees with $x$ outside $J$ and satisfies $f(y)=-1$. The input obtained by setting the coordinates in $J$ to $-1$ is coordinatewise at most $y$: on $J$ this follows because $-1$ is the least sign, and outside $J$ the inputs agree. Monotonicity therefore makes its function value at most $f(y)=-1$. Since every sign is at least $-1$ (`neg_one_le_sign`), that value equals $-1$. Conversely, if the input formed by setting all coordinates in $J$ to $-1$ has value $-1$, it is itself a witness: outside $J$ it agrees with $x$, and it has the required function value.

**Key facts.** `FABL.neg_one_le_sign`.
