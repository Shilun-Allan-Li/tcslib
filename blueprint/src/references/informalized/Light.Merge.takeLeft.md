<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Merge.lean :: Light.Merge.takeLeft -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Taking the Left Merge Entry

**Claim.** Under the merge preconditions and invariant at indices $i,j$, if $i<|l|$ and the remaining merge begins with $l_i$, executing the left-entry step is safe and establishes the invariant with progress $i+j+1$.

**Proof.** Unpack the invariant: the state has the prescribed frame, its memory agrees with the original memory outside the destination interval, and the output list has length $i+j$, is stored at the destination, and followed by the merge of the remaining tails gives the full merge. The source segment condition and preservation outside the destination show that the current memory at source address $a+i$ contains $l_i$ (`Seg.get`). The step writes this value at destination address $dst+|out|$; since $|out|=i+j$, this is the address represented by the program's destination-plus-progress expression. The bounds and disjointness in the preconditions ensure the source read and destination write are safe, and that the write lies within the destination interval. The resulting memory still agrees with the original outside that interval (`SameOutside.update`). Appending $l_i$ to the output gives a list of length $i+j+1$ stored at the destination (`Seg.snoc`). Finally, the assumed decomposition of the tail merge, together with the old invariant equation, shows that this enlarged output followed by the new tail merge is still the full merge. The updated frame records $i+1,j$, so the new total progress is $i+j+1.

**Key facts.** `Light.Seg.get`, `Light.SameOutside.update`, `Light.Seg.snoc`, `Light.update_frame_setLocal`.
