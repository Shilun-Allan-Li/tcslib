<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.extraVal_iff_prefix_all_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Auxiliary valuation as a false-prefix condition

**Claim.** When $j+2\le |L|$, the auxiliary valuation associated with $\alpha$, $L$, and $j$ holds exactly when every one of the first $j+2$ literals of $L$ is false under $\alpha$.

**Proof.** This is the defining condition for the auxiliary valuation: it says that every literal among the first $j+2$ entries of $L$ is false. The length hypothesis ensures that this prefix is within the list; both sides express the same condition.
