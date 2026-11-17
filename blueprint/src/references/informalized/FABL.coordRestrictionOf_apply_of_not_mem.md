<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordRestrictionOf_apply_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction at a fixed coordinate

**Claim.** At any coordinate $i\notin J$, the determined coordinate restriction fixes the coordinate to $1$ when its assigned sign is $1$, and to $-1$ otherwise.

**Proof.** Since $i\notin J$, the definition does not select the free case. It therefore compares the assigned sign at $i$ with $1$: equality selects the restriction fixing the coordinate to $1$, and failure of equality selects the restriction fixing it to $-1$.
