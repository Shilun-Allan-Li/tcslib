<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_label -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Translated Labels in the Statement Support

**Claim.** If an optional label belongs to the label support of the compilation with the halt label adjoined, then its translated label belongs to the compiled program’s finite statement support.

**Proof.** Separate the two possibilities for the optional label. If it is absent, its translation is absent, and the halt-marker support fact places that element in the statement support (`bridge_none`). If it is present, membership in the support with the halt label adjoined implies that the label itself belongs to the underlying label support. The translated label is one of the statements generated from that label, so it belongs to the union defining the statement support: use the label as the union index and the fact that each label’s translation contains its own translated label.

**Key facts.** `Turing.bridge_none`.
