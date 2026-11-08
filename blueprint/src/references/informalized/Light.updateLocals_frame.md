<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.updateLocals_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a framed list of locals

**Claim.** For every finite list of index-value pairs and every integer list, applying the updates to the function represented by the zero-padded list agrees with successively updating the list and then taking its frame.

**Proof.** Proceed by induction on the list of pairs. With no pairs, both sides are the original framed function. For a first pair $(x,z)$ followed by the remaining pairs, the definition of `updateLocals` first updates the framed function at $x$ to $z$. The single-update identity (`Light.update_frame_setLocal`) identifies this with the frame of the list after setting entry $x$ to $z$. Apply the induction hypothesis to the remaining pairs and this modified list; the result is exactly the frame of the successively updated list.

**Key facts.** `Light.update_frame_setLocal`.
