<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.PAL_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Palindrome Decidability

**Claim.** The palindrome language belongs to polynomial time: there are natural numbers $c$ and $a$ and a finite deterministic machine deciding it in at most $a(n^c+1)$ steps on inputs of length $n$.

**Proof.** The preceding linear-time palindrome result gives a machine running in the time bound $T(n)=n+1$. The general comparison principle `mem_P_of_dtime_le` says that a language decidable in time $T$ belongs to polynomial time whenever $T(n)\le c(n^d+1)$ for some constants $c,d$. Here take both constants to be $1$: for every $n$, $n+1=1\cdot(n^1+1)$. Applying that principle yields the polynomial-time membership.

**Key facts.** `Complexity.PAL_mem_DTIME_linear`, `Complexity.mem_P_of_dtime_le`.
