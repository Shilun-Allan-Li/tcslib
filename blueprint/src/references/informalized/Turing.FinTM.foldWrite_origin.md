<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldWrite_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writes Preserve the Origin Flag

**Claim.** For either side, any possibly blank folded cell $w$, and any possibly absent symbol $a$, the origin flag after writing $a$ into $w$ equals the origin flag before the write.

**Proof.** Unpack $w$ into its origin flag and two side entries. A write replaces only the entry on the chosen side and leaves the origin flag unchanged. Packing this result and unpacking it recovers the same folded symbol (`foldUnpack_pack`), including when the result is the canonical blank. Its origin flag is therefore the original one.

**Key facts.** `Turing.FinTM.foldUnpack_pack`.
