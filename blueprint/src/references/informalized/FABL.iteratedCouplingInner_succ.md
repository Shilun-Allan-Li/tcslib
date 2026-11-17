<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.iteratedCouplingInner_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor formula for iterated coupling

**Claim.** At length $n+1$, the iterated coupling expectation is the expectation over one pair with law $\kappa$ of the length-$n$ iterated coupling applied to the functions obtained by appending that pair's respective entries.

**Proof.** Unfolding the recursive definition at a successor length gives exactly the expectation over $z\sim\kappa$ of the length-$n$ iterated coupling, with $z$'s first entry appended to the input of $f$ and its second entry appended to the input of $g$.
