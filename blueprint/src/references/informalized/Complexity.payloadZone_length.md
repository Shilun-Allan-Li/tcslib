<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.payloadZone_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zone length

**Claim.** The payload zone of length $n$ starting at $z$ has list length exactly $n$, for either caching flag.

**Proof.** Induct on $n$. At length zero the zone is empty. At length $n+1$, its definition places one row before the zone of length $n$; its length is therefore one plus the length of that tail, which is $1+n=n+1$ by induction.
