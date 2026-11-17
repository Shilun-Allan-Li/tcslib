<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionCanAttain_one_iff_bribe_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attaining Plus One by a Coalition

**Claim.** For a monotone function, there is an input agreeing with $x$ outside $J$ on which the function equals $1$ if and only if setting every coordinate in $J$ to $1$ makes the function equal $1$.

**Proof.** Suppose a witness $y$ agrees with $x$ outside $J$ and has $f(y)=1$. Then $y$ is coordinatewise at most the input formed by setting every coordinate in $J$ to $1$: on $J$, every sign is at most $1$ (`sign_le_one`), and outside $J$ the inputs agree. Monotonicity implies that the latter input has function value at least $1$. As a sign, that value is also at most $1$, so it equals $1$. Conversely, if this input has function value $1$, it is itself a witness because it agrees with $x$ outside $J$.

**Key facts.** `FABL.sign_le_one`.
