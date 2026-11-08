<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_stripLast_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last-Marker Stripping with Bounded Space

**Claim.** There are a finite Boolean Turing machine and a constant $c$ that compute the specified last-marker stripping output in at most $c(|x|+1)^2$ steps and use at most $c(|x|+1)$ work-tape cells at every time.

**Proof.** Take the linear-time stripping machine, with time constant $a$. Its computation up to any time uses at most the number of work tapes times the elapsed time plus one; hence its space on input $x$ is at most $M.k\,(a(|x|+1)+1)$. Set $c=a+M.k(a+1)$. For time, the linear bound $a(|x|+1)$ is at most $a(|x|+1)^2$, since $|x|+1\ge1$; enlarge the constant to the chosen $c$. For space, $a(|x|+1)+1\le(a+1)(|x|+1)$, and the chosen $c$ dominates $M.k(a+1)$, giving the required linear bound.

**Key facts.** `Turing.FinTM.f2_strip_linear`, `Turing.FinTM.f2_space_of_time`, `Turing.FinTM.ComputesInTime.mono`.
