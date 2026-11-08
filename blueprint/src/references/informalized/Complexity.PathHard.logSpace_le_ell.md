<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.logSpace_le_ell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Space Bounded by Bit Length

**Claim.** For every natural number $m$, the base-$2$ logarithm of $m$, rounded down, plus $1$ is at most the number of binary digits of $m+1$.

**Proof.** The number of binary digits of $m+1$ is `Nat.size (m+1)` by `ell_eq_size`. If $m=0$, the claimed bound follows directly. For positive $m$, the inequalities $2^{\lfloor\log_2 m\rfloor}\le m$ and $m+1<2^{\operatorname{size}(m+1)}$ imply $\lfloor\log_2 m\rfloor<\operatorname{size}(m+1)$: otherwise the corresponding powers of $2$ would contradict these inequalities. Since both sides are integers, adding $1$ to the logarithm yields the desired bound.

**Key facts.** `Complexity.PathHard.ell_eq_size`.
