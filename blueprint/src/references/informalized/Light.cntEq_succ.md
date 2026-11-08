<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.cntEq_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Formula for an Equality Count

**Claim.** The number of indices below $j+1$ at which $kf$ equals $t$ is the count below $j$, plus $1$ if $kf(j)=t$ and plus $0$ otherwise.

**Proof.** The prefix below $j+1$ consists of the prefix below $j$ together with the single new index $j$. The count therefore increases by one precisely when that index satisfies $kf(j)=t$, giving the stated formula.
