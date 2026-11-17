<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.spaceConstructible_logSpace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic space constructibility

**Claim.** The function $L(n)=1+\lfloor\log_2 n\rfloor$ is space constructible: it bounds itself, and a finite binary Turing machine outputs the binary representation of $L(|x|)$ using at most a constant multiple of $L(|x|)$ work-tape cells.

**Proof.** The lower-bound condition is equality, since the required space bound is $L$ itself. The machine supplied by `b3a_log_machine` outputs the binary digits of $L(|x|)$ and uses at most $A(L(|x|)+1)$ cells for some positive integer $A$. Since $L(n)\ge1$, we have $L(n)+1\le2L(n)$. Hence its space usage is at most $2A L(|x|)$. Taking the constructibility constant to be $2A$ proves the claim.

**Key facts.** `Complexity.b3a_log_machine`.
