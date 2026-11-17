<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.mem_takeWhile_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in an Initial Segment

**Claim.** For a pairwise strictly increasing list, an element belongs to the initial segment of entries less than $b$ exactly when it belongs to the list and is less than $b$.

**Proof.** Proceed by induction on the list. The empty list has no such elements. For a list with head $x$ and tail $xs$, if $x<b$, the initial segment consists of $x$ followed by the initial segment of $xs$. The head is included precisely when the queried element equals $x$, and the induction hypothesis handles membership in the tail. If $x\not<b$, no entry is taken: pairwise strict increase says every entry of $xs$ is greater than $x$, so every tail entry is also not less than $b$. In this case both sides of the claimed equivalence are false.
