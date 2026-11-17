<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.polyUnaryTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Polynomial Output Bound

**Claim.** For every $C,e\in\mathbb N$, the machine $\mathrm{polyUnaryTM}(C,e)$ computes $C(|x|+1)^e$ copies of $1$ on every Boolean input $x$, within $(C+5e+4)(|x|+1)^e$ steps.

**Proof.** Fix $x$ and split on the exponent. When $e=0$, the machine is the constant-output machine for $C$ copies of $1$. Its computation takes $C+1$ steps, which is at most $(C+4)(|x|+1)^0=C+4$; this follows by extending the computation to the claimed time using time monotonicity (`ComputesInTime.mono`). For $e=d+1$, the definition selects the catalog unary machine, and its established computation bound gives the required output and time directly (`catalogPoly_unary_computes`).

**Key facts.** `Turing.FinTM.constTM_computes`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.catalogPoly_unary_computes`.
