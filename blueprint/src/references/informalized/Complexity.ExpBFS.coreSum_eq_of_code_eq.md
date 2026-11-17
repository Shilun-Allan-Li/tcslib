<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.coreSum_eq_of_code_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Codes Determine Core Data

**Claim.** For configurations $C$ and $D$ whose work-tape heads and nonblank cells lie within the window of size $s$, equality of their configuration codes implies equality of their core data and output summaries.

**Proof.** The code of a configuration is the binary value of its configuration word. By the identity relating a code’s binary expansion to its configuration word (`Complexity.Codec.bits_cfgCode`), equal codes give equal configuration words. The theorem that equal configuration words determine equal core data and output summaries under the stated window hypotheses (`Complexity.Codec.coreSum_eq_of_cfgWord_eq`) then yields the result.

**Key facts.** `Complexity.Codec.bits_cfgCode`, `Complexity.Codec.coreSum_eq_of_cfgWord_eq`.
