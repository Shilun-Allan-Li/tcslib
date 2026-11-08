<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.dm_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubling into a Scratch Register

**Claim.** If all registers are bounded by $B$ and $T+2S\le B$, the machine reaches phase zero of the move instruction with $S=0$ and $T=T_{\mathrm{old}}+2S_{\mathrm{old}}$, leaving the other registers unchanged; every earlier configuration satisfies the guard and register bound.

**Proof.** The four phases at the doubling site repeatedly decrease $S$ and add two units to $T$ per unit removed from $S$. The source and destination registers are distinct, so these updates yield the endpoint with $S=0$ and the indicated value of $T$, while all other registers are unchanged. The stated bound on the final value of $T$, together with the initial register bounds, ensures the loop remains within $B$. The general doubling-move theorem gives precisely this guarded reachability (`Complexity.LogProg.dmove_run`): its register-distinctness and phase equations follow from the machine definition, and its bounds follow from `St.Bd.toV` and the hypothesis. Translating its register-vector endpoint back to the state record gives the claimed result.

**Key facts.** `Complexity.LogProg.TQBFARM.St.Bd.toV`, `Complexity.LogProg.dmove_run`.
