<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.bribeFunction_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-Set Bribing

**Claim.** Replacing the coordinates in the empty set by a fixed sign leaves the Boolean function unchanged.

**Proof.** To prove equality of the two functions, fix an input $x$ and compare their values. Both are obtained by applying $f$, so it suffices to show that bribing the empty set leaves the input unchanged. At each coordinate, membership in the empty set is false; hence the coordinate retains its original value. Thus the two inputs, and therefore their images under $f$, agree.
