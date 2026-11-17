<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitStep_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split-Step Length Bound

**Claim.** If the candidate has length at most $|w|+1$, then after one split-search step its length is still at most $|w|+1$.

**Proof.** There are two cases. If the candidate length is at most $|w|$, the step appends one bit, so its new length is at most $|w|+1$. Otherwise the hypothesis that its length is at most $|w|+1$ forces its length to equal $|w|+1$; the step leaves it unchanged. Both cases give the claimed bound.
