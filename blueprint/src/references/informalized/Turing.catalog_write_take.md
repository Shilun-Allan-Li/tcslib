<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_write_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extension of a Tape Prefix

**Claim.** For $r<|w|$, updating the tape containing the first $r$ symbols of $w$ in cells $a$ through $a+r-1$ so that cell $a+r$ contains $w_r$ yields the tape containing the first $r+1$ symbols, with all other cells retained from $f$.

**Proof.** Compare the two functions at an arbitrary cell $q$. If $q=a+r$, the update supplies $w_r$; since $r<|w|$, this is exactly the stored-word value at offset $r$. The extended interval includes this cell, while the original prefix interval does not. If $q\ne a+r$, the update leaves the old value unchanged. Membership in the two intervals can differ only at their newly added endpoint, so at every other cell the old and extended descriptions coincide. Hence the two tape functions agree everywhere.
