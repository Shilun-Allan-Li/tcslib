<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_track_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tracking Configuration Relocation

**Claim.** Relocating the canonical tracking configuration determined by $c,b,n$ into the recorder's tracking slots, while using the recorder's remaining tapes and head positions, gives exactly the recorder configuration in its tracking phase.

**Proof.** The tracking slots place the tracking configuration's counter tapes in the recorder's leading counter slots, skip the recorder's intervening clock tape, and place the source input buffer and work tapes in the corresponding trailing slots. At each slot, the relocated tape contents and head position agree with those specified by the recorder layout: the counter tapes carry the encodings determined by $n$ and have head position zero; the input buffer carries $y$ with its head positioned at $c$'s shifted input position; and the trailing work tapes and heads are those of $c$. The configuration relocation preserves the input position and output, and maps the tracking state $(c.	ext{state},b,	ext{inactive})$ to the recorder's tracking-phase state. Extensionality of configurations then gives equality field by field.
