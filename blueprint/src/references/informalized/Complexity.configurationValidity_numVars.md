<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationValidity_numVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable Count of the Validity Formula

**Claim.** Under the stated lower bound on $C$, the configuration-validity CNF has at most $C(s+n+1)$ variables.

**Proof.** First, every literal in every clause of the formula has index below $C(s+n+1)$ (`configurationValidity_literals`). The general CNF variable-count bound says that if all variables of a formula, after relabeling, lie below $N$, then its number of variables is at most $N$ (`codecCnf_numVars`). Apply it with the identity wire map and $N=C(s+n+1)$ to obtain the result.

**Key facts.** `Complexity.configurationValidity_literals`, `Complexity.codecCnf_numVars`.
