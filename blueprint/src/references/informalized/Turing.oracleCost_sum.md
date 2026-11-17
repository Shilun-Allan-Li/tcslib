<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleCost_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summed Oracle Cost Bound

**Claim.** If each $cost(r)$ for $r<t$ is at most $a(r+1)+a\,charge(r)$, then $a+\sum_{r=0}^{t-1}cost(r)$ is at most $a(t+1)^2+a\sum_{r=0}^{t-1}charge(r)$.

**Proof.** Induct on $t$. At $t=0$, both sums are empty and the inequality reduces to $a\le a$, since $a\le a$. For the successor case, apply the induction hypothesis to the first $t$ terms and use the assumed bound at $r=t$ for the new term. Splitting each sum into its first $t$ terms and its last term, the desired inequality follows by combining these bounds and simplifying the natural-number arithmetic.
