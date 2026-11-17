<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitCfg_mapState_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State-Renamed Configuration Reconstruction

**Claim.** Under the stated agreements, embedding $c$ with the supplied tape data and output prefix and then renaming its state by $f$ yields $d$.

**Proof.** First apply the state map $f$ to $c$. Its state now agrees with $d$ by hypothesis, while its input-head position, output, tape contents, and head positions are unchanged. The selected and outside tape agreements therefore still hold. The reconstruction result `Turing.embedEmitCfg_eq` applies to this state-mapped configuration and gives exactly $d$.

**Key facts.** `Turing.embedEmitCfg_eq`.
