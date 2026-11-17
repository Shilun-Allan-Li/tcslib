<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SegN.drop_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Taking a dropped segment

**Claim.** If the values of $\mu$ starting at $a$ agree with the natural-number entries of $l$, viewed as integers, then the values starting at $a+lo$ agree with the entries of $(l.drop\ lo).take\ w$, viewed as integers.

**Proof.** First apply the segment-drop property (Light.Seg.drop): after dropping the first $lo$ entries, the remaining list describes the values starting at $a+lo$. Then apply the segment-take property (Light.Seg.take) to restrict this agreement to the first $w$ entries. Mapping natural numbers to their integer representations commutes with both dropping and taking, so this is precisely the claimed natural-number segment agreement.

**Key facts.** `Light.Seg.drop`, `Light.Seg.take`.
