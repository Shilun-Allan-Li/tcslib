<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.mem_pool_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pool Address Characterization

**Claim.** For every natural number $N$ and integer $a$, $a$ belongs to the pool of size $N$ if and only if it lies between $c_{\mathrm{Pool}}(N)$ and $c_{\mathrm{Pool}}(0)$, inclusive, and $c_{\mathrm{Pool}}(0)-a$ is divisible by $4$.

**Proof.** Membership in the pool means that $a=c_{\mathrm{Pool}}(n)$ for some natural number $n\le N$. In this form, the explicit formula for pool addresses immediately gives the stated bounds and divisibility. Conversely, the bounds and divisibility imply that $a$ is of the form $-25-4n$ for a natural number $n$ between $0$ and $N$. Taking $n=((-25-a)/4)^{\mathrm{nat}}$ recovers the required pool index; the inequalities ensure it is within the allowed range, and the divisibility condition ensures the formula gives $a$.

**Key facts.** `Set.mem_ofPred_eq`.
