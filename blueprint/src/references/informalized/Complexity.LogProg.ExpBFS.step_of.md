<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.step_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Step to Reachability

**Claim.** If executing the deterministic instruction at label $\ell$ from the register values of $S$ reaches $c$ while satisfying $G(x,B,P)$ at every preceding time, then the machine configuration at $\ell$ with those register values, marking $M$, and head position $p$ also reaches $c$ with the same guard.

**Proof.** The configuration $\mathrm{cf}(\ell,S,M,p)$ satisfies $G(x,B,P)$ by the register bounds in $S.\mathrm{Bd}(B)$ and the head bounds on $p$ ($\mathrm{g\_of}$). Its first machine step executes the deterministic instruction $i$, since the machine instruction at $\ell$ is exactly $i$. By the definition of the machine step, this produces precisely the configuration obtained by applying the register step to $(\ell,S.\mathrm{toV})$, while leaving the marking and head position unchanged. Thus the given guarded reachability begins at the successor of $\mathrm{cf}(\ell,S,M,p)$. Prepending this one guarded step yields the desired reachability ($\mathrm{MReach.step}$).

**Key facts.** `Complexity.LogProg.ExpBFS.g_of`, `Complexity.LogProg.MReach.step`.
