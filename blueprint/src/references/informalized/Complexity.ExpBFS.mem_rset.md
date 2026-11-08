<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.mem_rset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Set Membership

**Claim.** A number belongs to the finite set of codes below $2^{K(N)(s+\ell(|x|)+1)}$ that are reachable by zero or more encoded $s$-window steps exactly when it is reachable by those steps.

**Proof.** Membership in the filtered finite set means both that the number is below the stated bound and that it satisfies the reachability relation. Thus membership immediately implies reachability. Conversely, every reachable code lies below that bound by the code-size estimate (`Complexity.ExpBFS.rcode_lt`), so it satisfies both conditions for membership in the filtered set.

**Key facts.** `Complexity.ExpBFS.rcode_lt`.
