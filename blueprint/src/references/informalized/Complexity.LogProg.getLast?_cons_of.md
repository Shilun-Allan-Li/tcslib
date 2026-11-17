<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.getLast?_cons_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last element under prefixing

**Claim.** If the last-element operation on a Boolean list $u$ returns $v$, then prefixing $u$ by any Boolean $b$ leaves that result unchanged.

**Proof.** If $u$ is empty, the hypothesis that its last-element result is `some $v$` is impossible. Otherwise write $u=c::u'$. The last-element operation on a list with at least two elements ignores the first element, so the last-element result of $b::u$ equals that of $u$, namely `some $v$.
