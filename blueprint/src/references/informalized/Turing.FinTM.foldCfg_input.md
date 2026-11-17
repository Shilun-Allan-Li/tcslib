<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldCfg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbols under folding

**Claim.** The possibly absent input symbol scanned in the folded configuration is the image under the alphabet embedding of the symbol scanned in the original configuration.

**Proof.** The folded configuration keeps the input-head position unchanged, while the folded input is obtained by applying the alphabet embedding to every symbol. The two boundary positions therefore remain the same: at either boundary both scanned symbols are absent. At an interior position, both configurations select the corresponding list entry, and the folded entry is precisely the embedding of the original one. Thus the scanned-symbol option in the folded configuration is the mapped original option.
