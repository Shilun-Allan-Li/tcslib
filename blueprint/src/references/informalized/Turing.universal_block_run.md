<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_block_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Bounds from Block Simulation

**Claim.** Under the stated start-time and bounded-block hypotheses, for every $n$ there is a time $t$ with $n\le t\le S+Bn$ at which the universal machine's configuration is related to the source machine's configuration at time $n$.

**Proof.** Induct on $n$. For $n=0$, choose the time $t\le S$ supplied by the start hypothesis. It is nonnegative, and therefore lies between $0$ and $S$. For the successor step, suppose time $t$ witnesses the result at stage $n$. The one-step block hypothesis supplies a length $d$ with $1\le d\le B$ that advances from this related pair to a pair related after one additional source step. Choose the new time to be $t+d$. The lower bound follows from $t\ge n$ and $d\ge1$. For the upper bound, combine $t\le S+Bn$ with $d\le B$ to obtain $t+d\le S+B(n+1)$. The run composition law identifies running first for the accumulated time and then for the block with running for their sum (`runFrom_add`); the successor-time law identifies the source run at stage $n+1$ with one step after stage $n$ (`runFrom_succ_eq_step'`). Thus the relation required at stage $n+1$ holds.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
