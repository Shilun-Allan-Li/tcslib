<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.succFieldTM_unary_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Copying Step

**Claim.** For the unary-phase configuration after `r` symbols of `w` have been scanned, one step scans symbol `w_r`, advances the source head, and—when copying is enabled—writes that symbol at the destination and advances its head. The resulting configuration is the one after `r+1` symbols, with unary control if the scanned symbol is true and done otherwise.

**Proof.** The source symbol currently under the head is `w_r`: the configuration’s source head is displaced by `r`, and the assumed tape reading identifies the symbol there. Thus the unary transition chooses its successor phase according to whether `w_r` is true. The source head moves one cell right. If copying is enabled, the destination head also moves right and the transition writes the scanned symbol there; distinctness of the two indices keeps this write separate from the source tape. The finite-prefix write identity (`catalog_write_take`) shows that this new write extends the destination’s written interval from the first `r` symbols to the first `r+1`. Every other tape is unchanged, while the input position and output are unchanged because this is a work-tape action with no output. These componentwise facts give exactly the configuration described.

**Key facts.** `Turing.catalog_write_take`.
