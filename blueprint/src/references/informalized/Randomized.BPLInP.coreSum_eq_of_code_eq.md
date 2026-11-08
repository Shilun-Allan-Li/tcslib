<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPCount.lean :: Randomized.BPLInP.coreSum_eq_of_code_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Core Determined by Its Code

**Claim.** If two configurations lie in the radius-$s$ space window and have equal configuration codes, then their cores agree, including their state, input-head position, work-tape contents and head positions, and their output summaries.

**Proof.** The binary-value representation of a configuration code recovers its configuration word (`Complexity.Codec.bits_cfgCode`). Therefore equal codes give equal configuration words. Since both configurations lie in the radius-$s$ window, equality of those words forces equality of their cores and output summaries (`Complexity.Codec.coreSum_eq_of_cfgWord_eq`).

**Key facts.** `Complexity.Codec.bits_cfgCode`, `Complexity.Codec.coreSum_eq_of_cfgWord_eq`.
