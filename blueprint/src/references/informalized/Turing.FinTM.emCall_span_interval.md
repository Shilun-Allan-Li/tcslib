<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_span_interval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closed Spans as Half-Open Intervals

**Claim.** For $\ell\le h$, the closed-span marker on $[\ell,h]$ equals the half-open interval marker starting at $\ell$ with width $(h-\ell+1)$ converted to a natural number.

**Proof.** Since $h-\ell+1$ is nonnegative, its natural conversion, viewed again as an integer, is exactly $h-\ell+1$. Therefore the upper bound $z<\ell+(h-\ell+1)$ is equivalent to $z\le h$. The lower bound remains $\ell\le z$, so the closed and half-open markers agree at each integer $z$.
