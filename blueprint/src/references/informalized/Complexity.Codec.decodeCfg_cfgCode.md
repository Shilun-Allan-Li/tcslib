<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.decodeCfg_cfgCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Code Decoding

**Claim.** For a configuration in the stated window, decoding its code at window size $s$ returns a configuration in that window with the same code and the same state, input-head position, work-tape contents and head positions, and output summary.

**Proof.** Use the original configuration $C$ as a witness that a window-valid configuration with code $\mathrm{cfgCode}(s,C)$ exists. By the definition of decoding, the selected witness $D$ is returned; it is window-valid and has that same code. Consequently its configuration word agrees with that of $C$: applying `bits_cfgCode` to the equality of codes identifies their words. The theorem that equal configuration words for two window-valid configurations imply equal core data and output summary (`coreSum_eq_of_cfgWord_eq`) now shows that $D$ and $C$ agree on all the listed components.

**Key facts.** `Complexity.Codec.bits_cfgCode`, `Complexity.Codec.coreSum_eq_of_cfgWord_eq`.
