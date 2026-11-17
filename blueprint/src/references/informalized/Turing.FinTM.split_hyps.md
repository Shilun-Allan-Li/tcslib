<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.split_hyps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split-Body Round Bounds

**Claim.** Under the stated exact-output and time-bound hypotheses on the source machine, the combined split-search body reaches its anchored empty-candidate configuration within the stated bound without an earlier anchor visit; each candidate round also has the stated bound and either halts with the encoded split or returns to the anchor with the next candidate.

**Proof.** For each input $w$, the body starts in the anchor state with an empty candidate. The initial-configuration identity (`splitBody_start`) therefore gives the required startup witness at time zero, with no earlier time to check.

For the round assertion, fix $w$ and a candidate $s$ with $|s|\le |w|+1$. By hypothesis the source machine, run for $B(|s|)$ steps on the bank prepared for $s$, halts with $C(|s|+1)^e$ ones and unchanged tape contents. The split-body round result (`splitBody_round`) turns this into a positive-duration round that has no strictly intermediate positive visit to the anchor. Its endpoint is a halt with the encoded prefix and suffix if $|s|+C(|s|+1)^e=|w|$; otherwise it returns to the anchor with the next candidate. Its duration is at most $B(|s|)+5|s|+3|w|+20$. Apply the assumed bound on $B$ and the envelope estimate (`splitBody_envelope`) with $l=|s|$ and $n=|w|$ to bound this by $((C+1+5e)2^e+40)(|w|+1)^{e+1}$. The theorem's displayed bound has coefficient 45 more, so it also holds.

**Key facts.** `Turing.FinTM.splitBody_start`, `Turing.FinTM.splitBody_round`, `Turing.FinTM.splitBody_envelope`.
