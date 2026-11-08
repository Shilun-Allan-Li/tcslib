<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.wo_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Outward Walk

**Claim.** Under the stated register and head bounds, the machine runs from the outward-walk configuration to the memory-operation configuration with the updated counters and head position, and every configuration before the endpoint satisfies the guard.

**Proof.** Proceed by induction on the walk length $k$. If $k=0$, the outward-walk counter is already zero, so the first instruction branches directly to the memory operation. The hypotheses give the register and head bounds there; the zero-step reach at the endpoint then yields the claimed run, with the state and head unchanged. For the successor case, write the length as $k+1$. Since $S.T=k+1>0$, the first instruction moves to the next outward-walk phase, the next decrements $T$ to $k$, and the following instruction increments $T2$ to $S.T2+1$. The register bounds persist: all unchanged registers retain their bounds, while the new value of $T2$ is at most $B$ by the hypothesis $S.T2+(k+1)\le B$. The machine then moves the head one cell right. The head remains within $[0,P]$, and the induction hypotheses apply to the updated state and head, with remaining length $k$. They give the rest of the run, ending with $T=0$, $T2=(S.T2+1)+k=S.T2+(k+1)$, and head $p+1+k=p+(k+1)$. At each of these initial transitions the corresponding register bound and head bound establish the guard; the induction hypothesis supplies it for every subsequent pre-endpoint configuration.

**Key facts.** `Complexity.LogProg.ExpBFS.step_of`, `Complexity.LogProg.ExpBFS.mright_of`, `Complexity.LogProg.ExpBFS.reach_cf`, `Complexity.LogProg.MReach.refl`.
