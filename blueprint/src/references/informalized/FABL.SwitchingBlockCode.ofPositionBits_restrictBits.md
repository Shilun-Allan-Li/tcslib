<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingBlockCode.ofPositionBits_restrictBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction of a Canonical Code

**Claim.** If a switching block code has bit $0$ at every position outside its designated position set, then constructing a code from that set and the restricted bits recovers the original code.

**Proof.** The two codes have the same position set. Compare their bit functions at each position. If the position belongs to the set, the reconstructed bit is the original bit by restriction. If it lies outside the set, the reconstructed bit is $0$, which equals the original bit by the canonicality hypothesis. Hence the bit functions agree everywhere, and the codes are equal.
