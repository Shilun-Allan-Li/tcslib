<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clFields_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Field Length Bound

**Claim.** For every finite list $ws$ of Boolean words and every word $w$ occurring in $ws$, the length of $w$ is at most the length of the packed encoding of $ws$.

**Proof.** Induct on $ws$. The empty case cannot contain $w$. For a nonempty list $u::us$, its packed encoding has length $2|u|+2+|\mathrm{clFields}(us)|$. If the occurrence is $u$, this total is at least $|u|$. Otherwise the occurrence lies in $us$, so the induction hypothesis bounds its length by the packed encoding of $us$, which is no longer than the full encoding. Thus the bound holds in either case.
