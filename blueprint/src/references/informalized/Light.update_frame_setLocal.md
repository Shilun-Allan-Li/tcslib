<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.update_frame_setLocal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a list frame at one index

**Claim.** For every integer list $l$, natural-number index $x$, and integer $z$, updating the function represented by the zero-padded list $l$ at index $x$ to value $z$ gives the function represented by the list obtained by setting entry $x$ to $z$, extending the list with zeros if necessary.

**Proof.** It suffices to compare the two functions at an arbitrary index $y$. The frame of the list after setting entry $x$ has value $z$ when $y=x$ and otherwise retains the original frame value; this is the pointwise description of setting a list entry (`Light.frame_setLocal`). The updated function has exactly the same values: it returns $z$ at $x$ and the original framed value at every other index. Thus the functions agree everywhere.

**Key facts.** `Light.frame_setLocal`.
