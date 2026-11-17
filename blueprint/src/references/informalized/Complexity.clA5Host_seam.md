<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Host_seam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padded Module Seam

**Claim.** Forwarding a padded module configuration produces the canonical shared-bank configuration: it preserves the tape word in the shared layout, prefixes the output by $\mathrm{pre}$, and tags a present module state or uses the module’s resolved return when the state is absent.

**Proof.** The padded-seam identity (`clA5Pad_seam`) identifies the padded configuration’s tape contents and head positions with those of the canonical shared-bank configuration. Forwarding leaves the input position unchanged, changes the output to $\mathrm{pre}$ followed by $\mathrm{out}$, and maps the optional module state through its tag, using the resolved return when that state is absent. Thus the two configurations agree in state, input position, and output directly; the padded-seam identity gives agreement of their tape contents and head positions. Agreement of all configuration components proves the claimed equality.

**Key facts.** `Complexity.clA5Pad_seam`.
