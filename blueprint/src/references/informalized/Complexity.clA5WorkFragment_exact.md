<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5WorkFragment_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Work Fragment Identity

**Claim.** For every time within the producer horizon, the work fragment from the stored visit table equals the serialized fragment of the pure work clause group at that time and tape, using the specified reference input length.

**Proof.** The exact stored-visit result identifies the stored code with the optional-time code for the previous visit. The exact-data result also identifies the packed input size and horizon with the reference size and producer horizon. Split according to whether a previous visit exists. If there is none, the stored code is empty and the work-fragment definition selects the group for the case with no previous visit, matching the definition of the pure work group. If the previous-visit time is $s$, the previous-visit specification gives $s<t$ and hence $s\le t\le T$. The code for $s$ is nonempty, so the stored fragment selects the case with a previous visit. Its decoded time is $s$ because decoding the binary representation of $s$ recovers $s$; the horizon bound ensures the capped decoding returns $s$ unchanged. This is exactly the group used by the pure work-group definition. In either case, serializing the matching groups gives the stated equality.

**Key facts.** `Complexity.clA5Visit_exact`, `Complexity.clA5Data_exact`, `Complexity.clPrev_spec`, `Turing.pairDecode_pairEncode`, `Complexity.clNum_bits`.
