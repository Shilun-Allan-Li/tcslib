<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.mem_finsetTransportPerm_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership under finite-set transport

**Claim.** The transport permutation sends an index into $B$ exactly when the index belongs to $A$.

**Proof.** Let $e$ be the bijection from the subtype of indices in $A$ to the subtype of indices in $B$ used to define the transport. Split on whether $i\in A$. If it is, the transport agrees with $e$ on that subtype, so its image lies in $B$; this gives both directions of the equivalence in this case. If $i\notin A$, the extension property of the transport says its image cannot lie in $B$, while the right-hand membership condition is also false. Thus the equivalence holds in either case.
