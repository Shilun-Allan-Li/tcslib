<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingBlockCode.canonical_ofPositionBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonicality of the position-bit code

**Claim.** The code constructed from a position set and bits on that set is canonical: every position outside the set has bit zero.

**Proof.** The constructed code has position set exactly $S$ (`FABL.SwitchingBlockCode.ofPositionBits_positions`). If $i$ lies outside the code’s position set, it therefore lies outside $S$. By construction, the code’s bit at any position outside $S$ is zero, which is precisely canonicality.

**Key facts.** `FABL.SwitchingBlockCode.ofPositionBits_positions`.
