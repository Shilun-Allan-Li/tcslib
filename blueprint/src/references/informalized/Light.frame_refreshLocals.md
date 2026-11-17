<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.frame_refreshLocals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Refreshing selected local values

**Claim.** After refreshing the indices in $xs$, the frame at $y$ is $loc(y)$ when $y$ occurs in $xs$, and otherwise retains its original value at $y$.

**Proof.** Proceed by induction on the list of indices to refresh. For the empty list, the frame is unchanged and $y$ does not occur, so the formula holds. For a list $x::xs$, first refresh the tail and then update index $x$ to $loc(x)$. By the single-update frame property (`Light.frame_setLocal`), the resulting value at $y$ is the updated value if $y=x$, and otherwise is the frame value after refreshing the tail. If $y=x$, it is $loc(y)$ and $y$ occurs in the list. If $y\ne x$, membership in $x::xs$ is equivalent to membership in $xs$, and the induction hypothesis gives the asserted value.

**Key facts.** `Light.frame_setLocal`.
