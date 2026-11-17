<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.tRun_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Run in a Paired Encoding

**Claim.** For every natural number $n$ and Boolean list $z$, the initial run of true entries in the pairing of the length-$n$ all-true list with $z$ has length $2n$.

**Proof.** By the paired-encoding identity, the encoded list is the doubled first list, followed by the separator $[\mathrm{false},\mathrm{true}]$ and then $z$. Doubling the length-$n$ all-true list gives the length-$2n$ all-true list. Since the next entry is false, taking the initial run of true entries stops exactly at that separator, so its length is $2n$.

**Key facts.** `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`.
