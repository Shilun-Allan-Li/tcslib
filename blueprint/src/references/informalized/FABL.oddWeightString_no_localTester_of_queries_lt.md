<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.oddWeightString_no_localTester_of_queries_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Parity Query Lower Bound

**Claim.** If a nonadaptive randomized tester queries Boolean strings of positive length $n$ at fewer than $n$ positions, it cannot accept every odd-parity string perfectly while also having rejection probability strictly greater than the rate times $\varepsilon$ on every string that is farther than $\varepsilon$ from all odd-parity strings, for every $\varepsilon\in[0,1]$.

**Proof.** Assume such a tester and rate exist. Fix any seed in the support of its randomness. Since it makes fewer than $n$ queries, some coordinate $i$ is never queried (\texttt{exists\_unqueried\_coordinate}). The string that is true only at $i$ has odd parity (\texttt{singletonTrueString\_isOddWeight}), so perfect acceptance on all odd strings implies acceptance on this string for every supported seed; this follows from the characterization of acceptance probability one by acceptance on the support (\texttt{acceptanceProbability\_eq\_one\_iff\_accepts\_on\_support}). Because coordinate $i$ is unqueried, this string and the all-false string produce identical transcripts for that seed (\texttt{singletonTrueString\_transcript\_eq}). Thus every supported seed accepts the all-false string, and the same characterization gives acceptance probability one there. Now take $\varepsilon=0$. The all-false string differs from every odd-parity string, so its relative Hamming distance from each is positive; hence it is farther than zero from every odd string. The assumed soundness condition therefore says its rejection probability is strictly greater than $rate\cdot 0=0$. But acceptance probability one makes its rejection probability zero, a contradiction.

**Key facts.** `FABL.exists_unqueried_coordinate`, `FABL.singletonTrueString_isOddWeight`, `FABL.acceptanceProbability_eq_one_iff_accepts_on_support`, `FABL.singletonTrueString_transcript_eq`.
