<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.sum_fin_ite_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum with one omitted term

**Claim.** For $j\in\{0,\ldots,m-1\}$ and $q\in[0,\infty]$, summing $0$ at $j$ and $q$ elsewhere gives $(m-1)\,q$, interpreted as the sum of $m-1$ copies of $q$.

**Proof.** Separate the indices where the summand is zero from those where it is $q$. The latter are exactly the indices other than $j$. Removing $j$ from the $m$-element index set leaves $m-1$ elements, so the sum consists of $m-1$ copies of $q$, which is the stated scalar multiple.
