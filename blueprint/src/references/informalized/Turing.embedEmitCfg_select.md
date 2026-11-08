<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitCfg_select -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selecting and Re-Embedding a Configuration

**Claim.** Selecting the tapes indexed by $\sigma$ from a configuration, then embedding them back with the original contents and head positions on the other tapes and the original output as prefix, recovers the configuration exactly.

**Proof.** Apply `Turing.embedEmitCfg_eq` with the selected configuration as the smaller configuration and the original configuration as the target. Their states and input-head positions agree by selection. The output condition reduces to the original output followed by the empty selected output, which is the original output. On selected tapes, selection recovers the original contents and head positions; on unselected tapes, the supplied data are those of the original configuration. Hence all required field agreements hold.

**Key facts.** `Turing.embedEmitCfg_eq`.
