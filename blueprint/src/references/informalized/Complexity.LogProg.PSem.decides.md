<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.decides -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Halting Length and Output Probabilities

**Claim.** If the starting configuration has probabilistic semantics with probability $p$, then some length $N$ makes every choice sequence of length $N$ halt while satisfying $G$ at each earlier live configuration, and its true and false output probabilities are $p$ and $1-p$.

**Proof.** 1. The semantics hypothesis includes inductive termination of the starting configuration. The termination-to-uniform-length result (Complexity.LogProg.NTerm.nhalts) therefore supplies a length $N$ for which all runs of length $N$ halt and satisfy the guard at earlier live steps; that is, it gives $\mathrm{NHalts}$ at the starting configuration with guard $G$.

2. The probability clause of the semantics hypothesis applies at this same length, but requires only that all runs halt, with the trivial guard that holds at every configuration. Forgetting the guard condition in the already obtained $\mathrm{NHalts}$ statement gives this unconditional halting property (Complexity.LogProg.NHalts.mono). Applying the probability clause at $N$ yields the stated true and false probabilities.

**Key facts.** `Complexity.LogProg.NTerm.nhalts`, `Complexity.LogProg.NHalts.mono`.
