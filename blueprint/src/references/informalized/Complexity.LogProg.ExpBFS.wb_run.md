<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.wb_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Return Walk

**Claim.** Starting from the return-walk phase with $T2=k$, the machine reaches the corresponding exit with $T2=0$, unchanged marking, and head at $p-k$, with every preceding configuration satisfying the register and head guard.

**Proof.** Proceed by induction on $k$. For $k=0$, the return-walk phase immediately exits because $T2=0$. The configuration is already the required endpoint, and reflexive guarded reachability applies; the equality of states and head positions follows from $p-0=p$ ($\mathrm{MReach.refl}$ and $\mathrm{reach\_cf}$). For the successor case, the phase first checks that $T2$ is nonzero, decrements it, increments the return-walk counter as prescribed, and moves the head one cell left. The equality $T2=k+1$ ensures the nonzero branch is taken. After these instructions, the register state has $T2=k$ and remains bounded, while the head is at $p-1$; the hypotheses ensure this head remains in the allowed interval. The machine’s left-move step is justified by the bounded left-move reachability fact ($\mathrm{mleft\_of}$). Apply the induction hypothesis to this state and head: since $(p-1)-k=p-(k+1)$, it reaches the required exit with $T2=0$, unchanged marking, and the claimed final head position. The guarded reachability segments concatenate using the stated endpoint-identification and reachability facts.

**Key facts.** `Complexity.LogProg.ExpBFS.St.toV_T2`, `Complexity.LogProg.ExpBFS.step_of`, `Complexity.LogProg.ExpBFS.mleft_of`, `Complexity.LogProg.ExpBFS.reach_cf`, `Complexity.LogProg.MReach.refl`.
