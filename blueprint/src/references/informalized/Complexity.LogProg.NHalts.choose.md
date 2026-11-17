<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NHalts.choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting After a Nondeterministic Choice

**Claim.** When the instruction at $l$ chooses between $l_1$ and $l_0$, the guard holds at $(l,v,r)$ and both successor configurations satisfy the halting and intermediate-guard property for length $N$, every run from $(l,v,r)$ has that property for length $N+1$.

**Proof.** Take an arbitrary choice word of length $N+1$. It is nonempty, so write it as its first bit followed by a suffix of length $N$. The first choice sends $(l,v,r)$ to $(l_1,v,r)$ when the bit is true and to $(l_0,v,r)$ when it is false (`nastep_choose`). The run decomposition law identifies the full run with the suffix run from that selected successor (`narun_cons`). The corresponding hypothesis for that successor therefore gives halting at the end. For an intermediate time $t<N+1$, split into two cases. At $t=0$, the configuration is the initial one, so the guard follows from the assumption. If $t=s+1$, the prefix of length $t$ consists of the first choice and the first $s$ suffix choices; the decomposition identifies its configuration with the length-$s$ prefix run from the selected successor. Since $s<N$, the successor hypothesis gives the guard whenever that configuration is nonhalted.

**Key facts.** `Complexity.LogProg.narun_cons`, `Complexity.LogProg.nastep_choose`.
