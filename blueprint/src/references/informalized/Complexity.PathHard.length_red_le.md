<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.length_red_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bound on Reduction Length

**Claim.** For every machine and parameter $c_0$, there are natural numbers $C,c$ such that the reduction output on every input $x$ has length at most $C(|x|+1)^c$.

**Proof.** Set $e=codeK(N)(c_0+1)$, $D=2^{codeK(N)+2}2^e$, and choose $C=2D^2+2D+7$ and $c=2e$. The vertex bound `nV_le` gives $N\le Dq$, where $q=(|x|+1)^e$. Since $q\ge1$, we have $q\le q^2$ and hence $N^2\le D^2q^2$. By the exact length formula (`length_red`), the output length is $2N^2+2N+7$. Bound its three terms using $N^2\le D^2q^2$, $N\le Dq^2$, and $7\le7q^2$, respectively. The result is at most $(2D^2+2D+7)q^2=C(|x|+1)^{2e}$, as required.

**Key facts.** `Complexity.PathHard.length_red`, `Complexity.PathHard.nV_le`.
