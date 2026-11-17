<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean :: Complexity.LogProg.takeWhile_pairEncode_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial True Segment of a Paired Encoding

**Claim.** For every natural number $n$ and Boolean list $w$, the initial segment of true entries in the pairing of the length-$n$ all-true list with $w$ is exactly the length-$2n$ all-true list.

**Proof.** The paired-encoding identity writes the list as the doubled first component, followed by $[\mathrm{false},\mathrm{true}]$ and then $w$. The doubled length-$n$ all-true list is the length-$2n$ all-true list. The initial true segment of a concatenation whose first part is all true and whose next part begins with false is precisely that first part. Thus the initial true segment is the length-$2n$ all-true list.

**Key facts.** `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`.
