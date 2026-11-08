<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.encodeList_eq_gbits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate-list encoding by gate strings

**Claim.** Encoding a finite list of gates by prefixing each gate encoding with one and terminating with zero equals the concatenation of those prefixed gate encodings in list order, followed by zero.

**Proof.** Induct on the gate list. The empty list encodes as the terminating zero, which is also the empty concatenation followed by zero. For a head gate and tail list, the recursive list encoding prefixes the head gate's encoding with one and appends the encoding of the tail. Applying the induction hypothesis to the tail yields its prefixed gate strings followed by the final zero, giving the asserted form.
