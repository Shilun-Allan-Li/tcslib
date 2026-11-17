<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_go -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-step state transition simulation

**Claim.** If the compiled program has no pending call at $(l,\mathrm{start})$ and its transition there sends every possible input symbol, with the encoded register contents scanned at cell $0$, to $(\mathrm{target},\mathrm{start})$ without changing tapes, output, or head positions, then it simulates the change from label $l$ to $\mathrm{target}$ while preserving the registers and output; its only earlier configuration satisfies the call and head bounds.

**Proof.** Take a run of length one. The one-step iteration identity (`Complexity.LogProg.rrun_one`) identifies its endpoint with a single compiled-program step. Because the call at $(l,\mathrm{start})$ is absent, the non-call step rule (`Complexity.LogProg.rstep_noncall`) says this is the ordinary machine transition. In the initial configuration, each work head is at cell $0$ and scans the binary word for its register value; thus the assumed transition equation applies, regardless of the input symbol. Its prescribed action changes only the state to $(\mathrm{target},\mathrm{start})$, so the registers and output remain unchanged and the endpoint is the claimed configuration. For the sole earlier time, $t=0$, the zero-step identity (`Complexity.LogProg.rrun_zero`) identifies the configuration with the initial one. Its call is absent by hypothesis, and all heads are at $0$, which lies in $[-1,W]$ because $W\ge 0$.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`, `Complexity.LogProg.rrun_zero`.
