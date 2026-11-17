<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenMachine.lean :: Complexity.LogProg.ISGen.St.greg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Bounds for Encoded States

**Claim.** If each of the seventeen natural-number quantities in a register state is at most $B$, then every configuration whose register values are given by that state has all register values at most $B$, for any machine label and any optional Boolean result.

**Proof.** Unpack the hypothesis into the seventeen individual bounds. The encoded state lists the quantities in order as $n,\lg,k,s,e,K,T,i,i1,cp,v,c,u,cnt,g,cur,stp$. For any register index, it is one of these seventeen positions, so the corresponding bound gives that register value at most $B$. The machine label and Boolean result do not affect the register values.
