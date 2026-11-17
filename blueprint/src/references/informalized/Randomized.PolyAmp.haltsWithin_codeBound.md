<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.haltsWithin_codeBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Within the Configuration Code Bound

**Claim.** If $N$ uses at most $sp(|y|)$ space on every choice word and every Boolean input $y$, if $sp(|x|)\le S$, and if every branch halts on $x$ within $T$ steps, then every branch halts on $x$ within $2^{K(N)(S+\log_2(|x|)+1)}$ steps.

**Proof.** Apply `haltsWithin_of_codes`, the configuration-counting result that converts a space bound and an upper bound on the number of configurations into a halting-time bound. Here the assumed space estimate supplies the required bound $sp(|x|)\le S$, and the proposed time bound is exactly the configuration count $2^{K(N)(S+\log_2(|x|)+1)}$. Thus the result applies with equality for the configuration-count parameter, carrying the given halting hypothesis to the desired time bound.

**Key facts.** `Randomized.BPLInP.haltsWithin_of_codes`.
