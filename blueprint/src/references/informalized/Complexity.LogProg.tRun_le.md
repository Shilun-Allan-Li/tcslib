<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.tRun_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial True Run Bound

**Claim.** For every finite Boolean list $x$, the length of its initial run of true entries is at most the length of $x$.

**Proof.** The initial run is obtained by taking a prefix of $x$, namely the entries retained by taking elements while they are true. A prefix cannot be longer than the list from which it is taken, so its length is at most $x.length$.
