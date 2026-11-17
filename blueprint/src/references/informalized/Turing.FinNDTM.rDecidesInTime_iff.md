<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Turing.FinNDTM.rDecidesInTime_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalent randomized time criteria

**Claim.** The two formulations of randomized time-bounded decision are equivalent: the member acceptance probability is at least two-thirds exactly when it is written as the constant threshold function with value two-thirds, while the halting and nonmember conditions agree.

**Proof.** For each input $x$, the first definition requires the bound $2/3\leq N.outputProb(x,T(|x|),[\mathrm{true}])$. In the second definition, substituting the constant function $p(n)=2/3$ gives precisely that same inequality. The halting and nonmember clauses are identical, so the predicates agree pointwise in $x$ and hence are equivalent.
