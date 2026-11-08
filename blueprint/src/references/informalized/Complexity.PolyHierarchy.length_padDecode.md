<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.length_padDecode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length preservation by padded decoding

**Claim.** For any Boolean words $s$ and $v$, the padded decoding of $v$ relative to $s$ has the same length as $s$.

**Proof.** Unfold the definition of padded decoding and split according to whether decoding finds a marker. If no marker is found, the result is $s$, so its length is immediate. If a candidate word is found, the definition either returns that candidate when its length equals $|s|$, or returns $s$ otherwise. In either branch the returned word has length $|s|$.
