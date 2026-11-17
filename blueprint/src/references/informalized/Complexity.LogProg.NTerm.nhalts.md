<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NTerm.nhalts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Halting Bound

**Claim.** If every branch from a configuration terminates under the guard, then there is a uniform length at which every choice string has halted, with the guard holding at each earlier live prefix.

**Proof.** Proceed by induction on the terminating-derivation of the configuration. If it is already halted, choose bound $0$: every length-zero run is halted, and there are no shorter prefixes to check (`NHalts.halted`).

For a live configuration at state $l$, the guard holds there, and both possible next configurations terminate. By induction, choose bounds $N_1$ and $N_0$ for the successors selected by choice bits true and false, respectively. Set $N=\max(N_1,N_0)+1$. Any choice string of length $N$ begins with a bit $b$ and a suffix of length $\max(N_1,N_0)$. The successor selected by $b$ has a halting bound no larger than this suffix length, so its run halts by the end; adding the first step shows the original run is halted at length $N$. This uses monotonicity of the halting property in the chosen length (`NHalts.mono_len`) and the decomposition of a run into its first choice and remaining suffix (`narun_cons`).

Now consider a prefix of length $t<N$. If $t=0$, it is the initial live configuration, so it satisfies the guard by hypothesis. If $t>0$, remove the first choice: the remaining prefix has length $t-1$ and is shorter than the successor's uniform bound. Whenever the original prefix is still live, the corresponding successor prefix is live as well, and the induction hypothesis gives the guard there. Reattaching the first transition identifies this with the guard condition for the original run at that prefix, as required.

**Key facts.** `Complexity.LogProg.NHalts.halted`, `Complexity.LogProg.NHalts.mono_len`, `Complexity.LogProg.narun_cons`.
