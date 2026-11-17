<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.length_vword -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a virtual word

**Claim.** For any nonempty finite list of segments, the virtual word's length is the accumulated length of the segments before the last, with two additional bits per separator, plus the rendered length of the last segment.

**Proof.** Induct on the list of segments. The empty-list case is impossible under the nonemptiness assumption. For a singleton, the virtual word is its rendered segment; the offset is zero and the indexed segment is that singleton, giving the formula. For a list with at least two segments, write it as $s::t::rest$. The induction hypothesis applies to the nonempty tail $t::rest$. The virtual word consists of the rendering of $s$, the two-bit separator, and the virtual word of that tail, so its length is $rlen(s)+2$ plus the tail length. The offset on the full list has the same first contribution, and the index for the last segment shifts to the corresponding index in the tail. If the tail is a singleton, that indexed segment is its sole element; if it has more elements, the same index-shift identity applies. In either case the induction hypothesis supplies the remaining length, and rearranging the natural-number sums yields the stated formula.

**Key facts.** `Complexity.LogProg.length_render`, `Complexity.LogProg.seg_cons_succ`.
