<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean :: Complexity.TQBFHard.vlen_le_vwid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding Length Bound

**Claim.** For every natural number $n$, the configuration-code length at radius $2d(n+1)^c$ is at most the width $A(n+1)^{c+1}$, with $A$ the coefficient specified by the machine and $d$.

**Proof.** Put $Q=(n+1)^c$ and $P=(n+1)^{c+1}$. Since $n+1\ge 1$, increasing the exponent from $c$ to $c+1$ gives $Q\le P$, and $1\le Q$. Also $n+1\le P$, because $n+1\ge1$ and $c+1\ge1$. The bound on binary encoding length gives $wP(n)\le n+1$. Expanding the definitions, the code length is $4dW(N)Q+W(N)+wP(n)+1$, while the width is $4dW(N)P+W(N)P+(12N.kd+3N.k+2|N.State|+8)P$. The first term of the code length is bounded by the corresponding width term using $Q\le P$; its $W(N)$ term is bounded using $1\le P$. Finally, $wP(n)+1\le n+2\le 2P$, and the coefficient $12N.kd+3N.k+2|N.State|+8$ is at least $2$. Thus the remaining code-length terms are bounded by the final width term, proving the result.

**Key facts.** `Complexity.TQBFHard.wP_le`.
