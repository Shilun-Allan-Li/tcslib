<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLastCode_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Last-Visit Coding

**Claim.** The function sending a Boolean word to the code of the index immediately before its last true entry, with the empty word returned when there is no true entry, is computable in polynomial time.

**Proof.** Use the polynomial-time machine that decodes a pair, finds the prefix before the last true entry of its second component, and re-encodes the pair, returning empty output when decoding or the search fails. Combine its input with the identity function and the constant empty word using the polynomial-time pairing construction. Applying the pair-processing machine then yields the prefix determined by the last true entry. Finally, map the result to its binary length code; the length-in-bits function is polynomial-time computable, and polynomial-time functions are closed under composition. The decoding identity for encoded pairs (Turing.pairDecode_pairEncode) confirms that this construction, when applied to the encoded pair of the empty word and the input flags, agrees with the desired last-visit code. If there is no true entry, the search returns no prefix and the output is empty, as required.

**Key facts.** `Turing.FinTM.computesFunInTime_stripLast`, `Complexity.clNative_linear`, `Turing.FinTM.computesFunInTime_const`, `Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.clNative_map`, `Complexity.clNative_pair`, `Complexity.polyTimeComputable_id`, `Complexity.PolyTimeComputable.comp`, `Turing.pairDecode_pairEncode`.
