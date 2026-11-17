<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loop_orbit_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant Under Iterated Transitions

**Claim.** If $R(x,u(x))$ holds for every finite Boolean word $x$, and each application of $s\mapsto T(x,s)$ preserves $R(x,s)$, then $R(x,s_i)$ holds for every $i$, where $s_i$ is obtained by iterating that map $i$ times from $u(x)$.

**Proof.** Fix $x$ and induct on the number $i$ of iterations. At zero iterations the result is the assumed base property $R(x,u(x))$. For the successor case, the iterate after $i+1$ steps is obtained by applying $s\mapsto T(x,s)$ once to the iterate after $i$ steps. The induction hypothesis gives the invariant for that previous iterate, and the preservation assumption gives it for the next one.
