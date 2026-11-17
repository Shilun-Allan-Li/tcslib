<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_write_middle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating an Interior Tape Symbol

**Claim.** Updating the cell at $z+|\mathrm{pre}|$ in the tape storing $\mathrm{pre}\,a\,\mathrm{rest}$ from $a$ to $b$ yields the tape storing $\mathrm{pre}\,b\,\mathrm{rest}$, with the original tape retained outside the stored segment.

**Proof.** Compare the two tape functions at an arbitrary position $q$. If $q=z+|\mathrm{pre}|$, the update sets its value to $b$. The stored-word definition at that position also gives $b$, since it is the symbol immediately after the prefix $\mathrm{pre}$. If $q$ is different, the update leaves the original value unchanged. Within the stored segment, the list entries of $\mathrm{pre}\,a\,\mathrm{rest}$ and $\mathrm{pre}\,b\,\mathrm{rest}$ agree everywhere except at that one position; outside the segment, both definitions retain the original tape. Thus the functions agree at every $q$.
