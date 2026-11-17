<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_decrement_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Register Decrement Run

**Claim.** If each of $count$ successive states instructs the machine to decrement register $r$ and move to the next state, then the run reaches $path(count)$ with register $r$ decreased by truncated subtraction of $count$, all other registers unchanged, and no answer. Every preterminal configuration satisfies the safety condition and keeps all registers at most $4|h|+4$.

**Proof.** Proceed by induction on $count$. For $count=0$, the initial and final configurations coincide, so the zero-step reachability property applies (Complexity.LogProg.AReach.refl). For the successor case, the first instruction decrements $r$ and moves from $path(0)$ to $path(1)$. The machine's step relation therefore gives the first transition; the initial configuration satisfies the safety condition by the drop-machine safety lemma (Complexity.drop_preS), and its register bound is the hypothesis. After this transition, register $r$ has value $v(r)-1$, while the others are unchanged. The updated registers remain bounded by $4|h|+4$ (Complexity.LogProg.register_update_le). Apply the induction hypothesis to the shifted path $i\mapsto path(i+1)$ and these updated registers. Its endpoint has register $r$ equal to $(v(r)-1)-count$, which is $v(r)-(count+1)$ under natural-number truncated subtraction; the other registers remain unchanged. The reachability composition lemma (Complexity.LogProg.AReach.step) joins the initial transition to that inductive run. The safety condition at configurations along the run is supplied by Complexity.drop_preS.

**Key facts.** `Complexity.LogProg.AReach.refl`, `Complexity.drop_preS`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.AReach.step`.
