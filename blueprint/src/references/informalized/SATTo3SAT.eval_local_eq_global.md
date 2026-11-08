<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.eval_local_eq_global -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on local literals

**Claim.** For a literal whose auxiliary variables, if any, have index $i$, the local assignment defined from the clause at index $i$ agrees with the global assignment on its truth value.

**Proof.** Split on whether the literal is positive or negative, and then on whether its variable is original or auxiliary. For an original variable, both assignments use $\alpha$, so their evaluations agree. For an auxiliary variable, locality forces its index to equal $i$. The local assignment therefore uses the clause-specific all-false-prefix valuation. The global assignment uses the clause stored at index $i$, which is the given clause by hypothesis; since $i$ is a valid clause index, its valuation is the same. Thus the underlying variable has the same truth value in either assignment. Taking its negation in the negative-literal case preserves the agreement.
