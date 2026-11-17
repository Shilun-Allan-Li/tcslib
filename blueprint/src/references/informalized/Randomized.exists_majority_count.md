<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPAmplify.lean :: Randomized.exists_majority_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Power Bound

**Claim.** For rational $\varepsilon,\eta$ with $0<\varepsilon\leq 1/2$ and $\eta>0$, some natural number $K$ satisfies $2(1-4\varepsilon^2)^{\lfloor K/2\rfloor}\leq\eta$.

**Proof.** The assumptions imply $0\leq 1-4\varepsilon^2<1$. For a number strictly between zero and one, its powers eventually become smaller than any prescribed positive bound; apply this fact with bound $\eta/2$ to obtain $n$ with $(1-4\varepsilon^2)^n<\eta/2$. Set $K=2n$, so that $\lfloor K/2\rfloor=n$. Multiplying the strict inequality by $2$ gives the required weak bound.
