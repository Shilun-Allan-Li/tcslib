<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeReach_trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Machine Reachability

**Claim.** For any multi-tape Turing machine on a fixed input and configurations $a,b,d$, if $b$ is reachable from $a$ and $d$ is reachable from $b$, then $d$ is reachable from $a$.

**Proof.** Choose step counts $s$ and $t$ witnessing the two reachability assumptions, so that running from $a$ for $s$ steps gives $b$, and running from $b$ for $t$ steps gives $d$. Running from $a$ for $s+t$ steps is the same as first running for $s$ steps and then for $t$ more, by the addition law for iterated machine runs (`Turing.MultiTapeTM.runFrom_add`). Substituting the two witnessed equalities shows that this run ends at $d$, proving reachability from $a$ to $d$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
