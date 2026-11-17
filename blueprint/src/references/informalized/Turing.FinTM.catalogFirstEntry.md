<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogFirstEntry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Entry into a Fixed State

**Claim.** If every configuration in state $q$ is fixed by one step, and a run reaches a configuration $d$ in state $q$ by time $T$, then it reaches $d$ at some time $t\le T$ with no earlier visit to state $q$.

**Proof.** Let $t$ be the least time at which the run from $c$ is in state $q$. Such a time exists because the run is at $d$ at time $T$, and $d$ is in state $q$. By minimality, no time $j<t$ has the run in state $q$, and $t\le T$. The configuration at time $t$ is fixed by one step, so it is fixed by every number of steps. The iteration law for runs, which says that running for $a+b$ steps is the same as running $a$ steps and then $b$ more, gives
\[
\operatorname{runFrom}(c,T)=\operatorname{runFrom}(\operatorname{runFrom}(c,t),T-t)=\operatorname{runFrom}(c,t),
\]
using $t\le T$. Since the left side is $d$, the run is at $d$ at time $t$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
