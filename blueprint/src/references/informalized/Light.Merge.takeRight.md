<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Merge.lean :: Light.Merge.takeRight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Taking the Right Merge Entry

**Claim.** Under the merge preconditions and invariant at indices $i,j$, if $j<|r|$ and the remaining merge begins with $r_j$, executing the right-entry step is safe and establishes the invariant with progress $i+j+1$.

**Proof.** Unpack the invariant to obtain the current output list $out$, its length $i+j$, its segment representation at the destination, and the equation relating it to the full merge. The original memory contains $r_j$ at source address $b+j$: preservation outside the destination and the source segment condition give this using `Seg.get`. The step writes that value at destination address $dst+|out|=dst+i+j$. The merge preconditions ensure the load and store are safe and the destination address is within its allocated interval. After the write, the memory still agrees with the original outside that interval (`SameOutside.update`). Appending $r_j$ to $out$ yields a represented output segment of length $i+j+1$ (`Seg.snoc`). The assumed decomposition of the tail merge then makes the new output followed by the remaining tails equal to the full merge. The new frame records indices $i,j+1$, whose sum is $i+j+1.

**Key facts.** `Light.Seg.get`, `Light.SameOutside.update`, `Light.Seg.snoc`, `Light.update_frame_setLocal`.
