<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.update_in -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating an entry within a segment

**Claim.** If a function agrees with a finite list on the segment starting at $a$, then updating its value at $a+i$ to $x$ makes it agree with the list obtained by replacing entry $i$ by $x$.

**Proof.** Fix an index $j$ in the replaced list. Its length is unchanged, so $j$ is also a valid index of the original list. If $j=i$, the updated function takes the value $x$ at $a+i$, and the replaced list has entry $x$ there. If $j\ne i$, the index $a+j$ differs from the update location $a+i$; hence the function is unchanged there. The original segment agreement gives the value $l_j$, which is also the entry at $j$ after replacing a different position.
