<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.mem_argSegs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Argument segment membership

**Claim.** For any segment in the list of argument segments formed from a list $ws$ of Boolean words, its word component occurs in $ws$.

**Proof.** Proceed by induction on $ws$. For the empty list there are no argument segments, so the assertion is vacuous. For a singleton list $[w]$, the only possible segment has word component $w$, which belongs to the list. For a list beginning $w::v::ws'$, the first argument segment has word component $w$, hence belongs to the original list. Any other segment comes from the argument segments of $v::ws'$; the induction hypothesis puts its word component in that tail, and therefore in the original list as well.
