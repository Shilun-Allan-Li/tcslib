<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.decodeCfg_eq_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failed Configuration Decoding

**Claim.** Decoding $c$ at window size $s$ returns no configuration exactly when there is no configuration for input $x$ that lies in the window and has code $c$ at that window size.

**Proof.** Unfold the decoder's definition and consider whether a witness configuration exists. If one exists, the decoder returns the chosen witness wrapped in `some`, so it is not `none`; if no witness exists, the decoder returns `none`. These two cases give the stated equivalence.
