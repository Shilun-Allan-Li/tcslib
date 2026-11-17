<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean :: Complexity.logSpace_le_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Log-space bound by the input parameter

**Claim.** For every $n\in\mathbb{N}$, $\ell(n)\le n+1$, where $\ell(n)=\lfloor\log_2 n\rfloor+1$ for positive $n$ and $\ell(0)=1$.

**Proof.** The elementary logarithm bound $\lfloor\log_2 n\rfloor\le n$ gives $\ell(n)=\lfloor\log_2 n\rfloor+1\le n+1$. This also covers $n=0$, with the stated convention $\ell(0)=1$.
