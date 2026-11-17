<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability After a Fair Choice

**Claim.** If the instruction at $l$ makes a fair choice between $l_1$ and $l_0$, and those branches have terminating semantics with acceptance probabilities $p_1$ and $p_0$, then the configuration at $l$ has terminating semantics with acceptance probability $(p_1+p_0)/2$.

**Proof.** 1. The choice instruction sends choice bit $1$ to $l_1$ and bit $0$ to $l_0$, leaving the valuation and result unchanged (`nastep_choose`). Thus both possible successors terminate by the assumed branch semantics, and the guard at $l$ supplies the guard condition for the initial step. The inductive definition of guarded termination then gives termination from $l$.

2. Any run length witnessing halting from this live configuration is positive; write it as $N+1$ (`succ_of_nhalts`). Fix such a length. Removing the first choice bit gives a halting run of length $N$ from each corresponding successor (`NHalts.of_choose`). The branch semantics consequently identifies the true-answer probabilities with $p_1,p_0$ and the false-answer probabilities with $1-p_1,1-p_0$.

3. Among all equally likely choice sequences of length $N+1$, the first bit splits them evenly between the two branches. Hence each answer probability from $l$ is the average of the corresponding branch probabilities (`randProb_narun_choose`). The true-answer average is $(p_1+p_0)/2$; the false-answer average is $((1-p_1)+(1-p_0))/2=1-(p_1+p_0)/2$. This proves the required semantics.

**Key facts.** `Complexity.LogProg.nastep_choose`, `Complexity.LogProg.succ_of_nhalts`, `Complexity.LogProg.NHalts.of_choose`, `Complexity.LogProg.randProb_narun_choose`.
