<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satChain_vars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable bounds along the chain

**Claim.** If every variable index in the clause formed by adjoining the head literal to the remainder is less than the starting cursor, then every literal in every clause produced by the chain has index less than the returned cursor.

**Proof.** Proceed by induction on the remainder, generalizing the head literal and starting cursor. When the remainder has fewer than three entries, the chain consists of the single clause containing the head and the remainder, and the hypothesis gives the desired bound. Otherwise write the remainder as $b::c::d::R$. The recursive call starts with head $(n,\mathrm{false})$, remainder $c::d::R$, and cursor $n+1$. Its input literals all have indices below $n+1$: the new head has index $n$, while each of the others already occurs in the original clause and hence has index below $n$. The induction hypothesis therefore bounds every literal in each recursively produced clause by the recursive call's returned cursor. The other clause produced at this stage is $[head,b,(n,\mathrm{true})]$. The first two indices are below $n$ by the original hypothesis, and the new literal's index $n$ is below the final cursor: the recursive cursor is at least its starting value $n+1$. Thus the bound holds for both the new clause and all clauses from the recursive call.
